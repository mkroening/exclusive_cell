//! This crate provides two thread-safe, non-blocking, no-std synchronization primitives: [`ExclusiveCell`] and [`CallOnce`].
//!
//! [`ExclusiveCell`] can be accessed at most once and provides mutable access to the stored contents:
//!
//! ```
//! use exclusive_cell::ExclusiveCell;
//!
//! static EXCLUSIVE_CELL: ExclusiveCell<usize> = ExclusiveCell::new(5);
//!
//! let number = EXCLUSIVE_CELL.take().unwrap();
//! assert_eq!(number, &mut 5);
//!
//! assert!(EXCLUSIVE_CELL.take().is_none());
//! ```
//!
//! [`CallOnce`] can only be called once sucessfully:
//!
//! ```
//! use exclusive_cell::CallOnce;
//!
//! static CALL_ONCE: CallOnce = CallOnce::new();
//!
//! assert!(CALL_ONCE.call_once().is_ok());
//! assert!(CALL_ONCE.call_once().is_err());
//! ```

#![no_std]

use core::{
    cell::UnsafeCell,
    fmt,
    sync::atomic::{AtomicBool, Ordering},
};

/// A synchronization primitive that can only be called once sucessfully.
///
/// It behaves similarily to `ExclusiveCell<()>` but with a more descriptive API.
///
/// # Examples
///
/// ```
/// use exclusive_cell::CallOnce;
///
/// static CALL_ONCE: CallOnce = CallOnce::new();
///
/// assert!(CALL_ONCE.call_once().is_ok());
/// assert!(CALL_ONCE.call_once().is_err());
/// ```
#[derive(Default, Debug)]
pub struct CallOnce {
    called: AtomicBool,
}

impl CallOnce {
    /// Creates a new `CallOnce`.
    ///
    /// # Examples
    ///
    /// ```
    /// use exclusive_cell::CallOnce;
    ///
    /// let call_once = CallOnce::new();
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self {
            called: AtomicBool::new(false),
        }
    }

    /// Mark this `CallOnce` as called.
    ///
    /// Only the first call returns `Ok`.
    /// All subsequent calls return `Err`.
    ///
    /// # Examples
    ///
    /// ```
    /// use exclusive_cell::CallOnce;
    ///
    /// let call_once = CallOnce::new();
    ///
    /// assert!(call_once.call_once().is_ok());
    /// assert!(call_once.call_once().is_err());
    /// ```
    #[inline]
    pub fn call_once(&self) -> Result<(), CallOnceError> {
        self.called
            .compare_exchange(false, true, Ordering::Relaxed, Ordering::Relaxed)
            .map(drop)
            .map_err(|_| CallOnceError)
    }

    /// Returns `true` if `call_once` has been called.
    ///
    /// # Examples
    ///
    /// ```
    /// use exclusive_cell::CallOnce;
    ///
    /// let call_once = CallOnce::new();
    /// assert!(!call_once.was_called());
    ///
    /// call_once.call_once().unwrap();
    /// assert!(call_once.was_called());
    /// ```
    #[inline]
    pub fn was_called(&self) -> bool {
        self.called.load(Ordering::Relaxed)
    }
}

/// The `CallOnceError` error indicates that [`CallOnce::call_once`] has been called more than once.
#[derive(Debug)]
pub struct CallOnceError;

impl fmt::Display for CallOnceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("call_once was executed more than once")
    }
}

/// A synchronization primitive which can be accessed only once.
///
/// This type is a thread-safe cell, and can be used in statics.
/// `ExclusiveCell` provides a mutable reference to the contents without RAII guards, but only on the first try.
///
/// # Relation with other types
///
/// `ExclusiveCell` is complementary to `OnceCell` with regards to `Mutex` and `RwLock`:
///
/// | `C`           | `Mutex`      | `RwLock`                        | `OnceCell` | `ExclusiveCell` |
/// | ------------- | ------------ | ------------------------------- | ---------- | --------------- |
/// | `&C` provides | `MutexGuard` | `RwLock{Read,Write}Guard`       | `&T`       | `&mut`          |
///
/// A `OnceCell` can be emulated using a `RwLock` by only ever calling `try_read` and leaking the `RwLockReadGuard`.
/// Similarily, `ExclusiveCell` can be emulated using a `RwLock` by only ever calling `try_write` and leaking the `RwLockWriteGuard`.
///
/// In contrast to `OnceCell` but similarly to `Mutex` and `RwLock`, the contents of a `ExclusiveCell` have to be initialized at creation.
///
/// # Similarities with `cortex_m::singleton`
///
/// `ExclusiveCell` can be used similarily to [`cortex_m::singleton`] to create a mutable reference to a statically allocated value.
/// In contrast to `cortex_m::singleton`, `ExclusiveCell` is thread safe and does not require using macros.
///
/// [`cortex_m::singleton`]: https://docs.rs/cortex-m/0.7.6/cortex_m/macro.singleton.html
///
/// # Examples
///
/// ```
/// use exclusive_cell::ExclusiveCell;
///
/// static EXCLUSIVE_CELL: ExclusiveCell<usize> = ExclusiveCell::new(5);
///
/// let number = EXCLUSIVE_CELL.take().unwrap();
/// assert_eq!(number, &mut 5);
///
/// assert!(EXCLUSIVE_CELL.take().is_none());
/// ```
#[derive(Debug)]
pub struct ExclusiveCell<T: ?Sized> {
    taken: CallOnce,
    data: UnsafeCell<T>,
}

unsafe impl<T: ?Sized + Send> Send for ExclusiveCell<T> {}
unsafe impl<T: ?Sized + Send> Sync for ExclusiveCell<T> {}

impl<T> ExclusiveCell<T> {
    /// Creates a new `ExclusiveCell` containing the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use exclusive_cell::ExclusiveCell;
    ///
    /// let exclusive_cell = ExclusiveCell::new(5);
    /// ```
    #[inline]
    pub const fn new(val: T) -> Self {
        Self {
            taken: CallOnce::new(),
            data: UnsafeCell::new(val),
        }
    }

    /// Unwraps the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use exclusive_cell::ExclusiveCell;
    ///
    /// let exclusive_cell = ExclusiveCell::new(5);
    /// let number = exclusive_cell.into_inner();
    ///
    /// assert_eq!(number, 5);
    /// ```
    #[inline]
    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<T: ?Sized> ExclusiveCell<T> {
    /// Takes the mutable reference to the wrapped value.
    ///
    /// Only the first call returns `Some`.
    /// All subsequent calls return `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use exclusive_cell::ExclusiveCell;
    ///
    /// let exclusive_cell = ExclusiveCell::new(5);
    ///
    /// let number = exclusive_cell.take().unwrap();
    /// assert_eq!(number, &mut 5);
    ///
    /// assert!(exclusive_cell.take().is_none());
    /// ```
    #[inline]
    #[must_use]
    pub fn take(&self) -> Option<&mut T> {
        self.taken
            .call_once()
            .ok()
            .map(|_| unsafe { &mut *self.data.get() })
    }

    /// Returns `true` if the mutable reference has been taken.
    ///
    /// # Examples
    ///
    /// ```
    /// use exclusive_cell::ExclusiveCell;
    ///
    /// let exclusive_cell = ExclusiveCell::new(5);
    /// assert!(!exclusive_cell.is_taken());
    ///
    /// let number = exclusive_cell.take().unwrap();
    /// assert!(exclusive_cell.is_taken());
    /// ```
    #[inline]
    pub fn is_taken(&self) -> bool {
        self.taken.was_called()
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this method borrows `ExclusiveCell` mutably, it is statically guaranteed
    /// that no borrows to the underlying data exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use exclusive_cell::ExclusiveCell;
    ///
    /// let mut exclusive_cell = ExclusiveCell::new(5);
    ///
    /// let number = exclusive_cell.get_mut();
    /// assert_eq!(number, &mut 5);
    ///
    /// assert!(!exclusive_cell.is_taken());
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data.get() }
    }
}

impl<T: Default> Default for ExclusiveCell<T> {
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl<T> From<T> for ExclusiveCell<T> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}
