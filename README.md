# Multiplicative rank along expanding affine paths of integers

[Read the paper (PDF)](expanding-affine-rank.pdf) · [Lean verification of the moment lemma](verification/RankBound.lean)

Fix a finite family of maps $x\mapsto ax+b$ with positive rational slopes and nonzero rational translations. Starting at any positive integer, choose a map at each step so that all $N+1$ values remain positive integers. If $\log(x_N/x_0)\ge\gamma N$ for a fixed $\gamma>0$, at least $cN/\sqrt{\log(2N)}$ of those values are multiplicatively independent. The constant $c>0$ depends only on the family and $\gamma$, not on the choices of maps or the starting value. Multiplicative independence means that the only product of integer powers of the selected values equal to 1 is the one with all exponents zero.

## What Lean checks

`RankBound.lacunary_endWeight` proves Lemma 3.1 of the paper. For real nodes whose absolute values shrink by a factor of at least two at each step, vanishing of successive positive power moments bounds the first weight in terms of the others. The proof also includes a rational variant: `RankBound.primePower_dvd_endWeight` proves divisibility of the first weight by a power of a prime, and `RankBound.exists_ne_zero_moment` gives a nonvanishing consequence. The choice of gaps along the integer path, the logarithmic comparison, and the final rank theorem are proved in the paper, **not** in Lean.

To check the proof, install [Elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
cd verification
lake exe cache get Mathlib.NumberTheory.Padics.PadicVal.Basic Mathlib.Basic.Real.Basic Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Tactic.Ring Mathlib.Tactic.Linarith
lake build
lake env lean RankBound.lean
```

The cache command is optional; it saves rebuilding mathlib dependencies. The project pins Lean `v4.35.0-rc4` and [mathlib at `1f414401`](https://github.com/leanprover-community/mathlib4/tree/1f414401f69059aa7eead47b53ee40bd38455eeb). The last command prints the axioms used by the three named theorems: `propext`, `Classical.choice`, and `Quot.sound`.

© 2026 maxilism. The paper, documentation, and original Lean verification code are licensed under [Creative Commons Attribution 4.0 International](LICENSE). External dependencies retain their own licenses.
