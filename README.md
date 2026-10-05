# Dafny Euclidean Algorithms

This project demonstrates the Euclidean algorithm in Dafny and proves its key correctness properties. It includes a greatest common divisor function for integers, a lemma about remainders, and an extended Euclidean method that returns Bézout coefficients.

`ExtendedEuclidean(a, b)` returns `g`, `u`, and `v` such that `g` is the greatest common divisor of `a` and `b`, and `u * a + v * b == g`. The `Main` method runs the algorithm for `10` and `7` and prints the result.

## Requirements

- [Dafny](https://dafny.org/) 4.x

## Verify

From the project directory, run:

```sh
dafny verify first.dfy
```

Dafny checks the function and method contracts, loop invariants, and lemmas. A successful verification reports the number of verified checks and no errors.

## Run the example

To verify and run `Main`, use:

```sh
dafny run first.dfy
```

The program prints the GCD and Bézout coefficients for `10` and `7`.
