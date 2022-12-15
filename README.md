# exclusive_cell

[![Crates.io](https://img.shields.io/crates/v/exclusive_cell)](https://crates.io/crates/exclusive_cell)
[![docs.rs](https://img.shields.io/docsrs/exclusive_cell)](https://docs.rs/exclusive_cell)
[![CI](https://github.com/mkroening/exclusive_cell/actions/workflows/ci.yml/badge.svg)](https://github.com/mkroening/exclusive_cell/actions/workflows/ci.yml)

This crate provides two thread-safe, non-blocking, no-std synchronization primitives:
* `ExclusiveCell` can be accessed at most once and provides mutable access to the stored contents.
* `CallOnce` can only be called once sucessfully.

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
