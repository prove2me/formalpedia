-- Prove2me | solution 1 for NumberField.Set.primeIdealZetaSum_eq_mul_of_card_fiber
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:31.71305+00:00
-- url     : https://prove2.me/submissions/a472baf3-4456-45d0-a53e-518cf47b0a6d

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Contracting prime sums and Dirichlet densities along a fibre count

Let `K` and `E` be number fields, `T` a set of height-one primes of `𝓞 E` and `S` one of `𝓞 K`,
and let `π` send each prime of `E` to a prime of `K`. Suppose that `π` maps `T` into `S`, that it
preserves absolute norms on `T`, and that every `𝔭 ∈ S` has exactly `c ≠ 0` preimages in `T`.
Then, for every real `s`,

```text
∑_{𝔓 ∈ T} N𝔓 ^ (-s) = c * ∑_{𝔭 ∈ S} N𝔭 ^ (-s),
```

and consequently `T` has Dirichlet density `δ` exactly when `S` has Dirichlet density `δ / c`.

The fibre count only matters away from a set of density zero. If `π` does not increase norms and
has boundedly many preimages in `T` over each prime of `S`, the prime sum over `T` is bounded by a
multiple of the prime sum over `S`, so preimages of a density-zero set have density zero. Hence the
exact count `c` is needed only for the primes of `S` outside a density-zero set `Z`, with a
uniform bound over `Z`.

The typical `π` is contraction `𝔓 ↦ 𝔓 ∩ 𝓞 K` for an extension `E / K`. It preserves norms exactly
on the primes of residue degree one over `K`, and the others have density zero, so only primes of
residue degree one need to be counted in the fibres; at most `[E : K]` primes of `E` lie over a
given prime of `K`, which supplies the uniform bound over `Z`. This is how a density computed over
an extension field is transported down to the base, as in the proof of the Chebotarev density
theorem, where a relative Frobenius fibre over the fixed field of a cyclic subgroup is counted
over the primes of the base field.

## Main results

* `NumberField.Set.primeIdealZetaSum_eq_mul_of_card_fiber`: the exact identity of prime sums.
* `NumberField.Set.hasDirichletDensity_iff_of_card_fiber`: the transfer of Dirichlet densities.
* `NumberField.Set.primeIdealZetaSum_le_mul_of_encard_fiber_le`: the prime-sum inequality for a
  bounded fibre count.
* `NumberField.Set.HasDirichletDensity.zero_of_encard_fiber_le`: density zero pulls back along a
  bounded fibre count.
* `NumberField.Set.hasDirichletDensity_iff_of_card_fiber_of_negligible`: the transfer of
  Dirichlet densities when the fibre count is exact only off a set of density zero.
* `NumberField.Set.hasDirichletDensity_contraction`: the transfer along contraction, counting only
  primes of residue degree one and only off a set of density zero.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.1.
-/

 section

open Filter IsDedekindDomain NumberField
open scoped symmDiff Topology

namespace NumberField.Set
end NumberField.Set
section NumberField.Set
open NumberField NumberField.Set

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E]
  {T : Set (HeightOneSpectrum (𝓞 E))} {S : Set (HeightOneSpectrum (𝓞 K))}
  {π : HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 K)} {c : ℕ}

/-- **Prime sums along a fibre count.** If `π` maps `T` into `S`, preserves absolute norms on `T`,
and every prime of `S` has exactly `c ≠ 0` preimages in `T`, then the prime sum over `T` is `c`
times the prime sum over `S`, at every real `s`. -/
theorem solution (hmaps : _root_.Set.MapsTo π T S)
    (hnorm : ∀ 𝔓 ∈ T, _root_.Ideal.absNorm 𝔓.asIdeal = _root_.Ideal.absNorm (π 𝔓).asIdeal) (hc : c ≠ 0)
    (hfiber : ∀ 𝔭 ∈ S, _root_.Nat.card {𝔓 // π 𝔓 = 𝔭 ∧ 𝔓 ∈ T} = c) (s : ℝ) :
    T.primeIdealZetaSum s = c * S.primeIdealZetaSum s := by
  classical
  let f : T → S := hmaps.restrict π T S
  let g : S → ℝ := fun 𝔭 ↦ (_root_.Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)
  -- The fibres of `f` are those of `π` over `S`, so each has `c` elements.
  have hcard (𝔭 : S) : _root_.Nat.card {t : T // f t = 𝔭} = c := by
    rw [← hfiber 𝔭 𝔭.2]
    refine _root_.Nat.card_congr
      { toFun := fun t ↦
          ⟨t.1.1, (hmaps.val_restrict_apply t.1).symm.trans (_root_.congrArg _root_.Subtype.val t.2), t.1.2⟩
        invFun := fun 𝔓 ↦
          ⟨⟨𝔓.1, 𝔓.2.2⟩, _root_.Subtype.ext ((hmaps.val_restrict_apply _).trans 𝔓.2.1)⟩
        left_inv := fun _ ↦ _root_.rfl
        right_inv := fun _ ↦ _root_.rfl }
  -- `c ≠ 0` makes the fibres finite: an infinite fibre would have `Nat.card` equal to `0`.
  have hfin (𝔭 : S) : _root_.Finite {t : T // f t = 𝔭} :=
    _root_.Nat.finite_of_card_ne_zero ((hcard 𝔭).symm ▸ hc)
  have hinner (𝔭 : S) : ∑' _ : {t : T // f t = 𝔭}, g 𝔭 = c * g 𝔭 := by
    have := _root_.Fintype.ofFinite {t : T // f t = 𝔭}
    rw [_root_.tsum_fintype, _root_.Finset.sum_const, _root_.Finset.card_univ, _root_.Fintype.card_eq_nat_card, hcard,
      _root_.nsmul_eq_mul]
  -- Regroup the sum over `T` along the fibres of `f`; `π` preserves the norm on `T`.
  have hT : T.primeIdealZetaSum s = ∑' x : Σ 𝔭 : S, {t : T // f t = 𝔭}, g x.1 := by
    rw [_root_.NumberField.Set.primeIdealZetaSum_def, ← (_root_.Equiv.sigmaFiberEquiv f).tsum_eq]
    refine _root_.tsum_congr fun ⟨𝔭, t, ht⟩ ↦ ?_
    subst ht
    simp only [_root_.Equiv.sigmaFiberEquiv_apply, hnorm t.1 t.2, g, f, hmaps.val_restrict_apply]
  -- Both sides are summable together, so off summability both are the junk value `0`.
  rw [hT, _root_.NumberField.Set.primeIdealZetaSum_def]
  by_cases hsum : _root_.Summable fun x : Σ 𝔭 : S, {t : T // f t = 𝔭} ↦ g x.1
  · rw [hsum.tsum_sigma, _root_.tsum_congr hinner, _root_.tsum_mul_left]
  · -- The regrouped family is summable exactly when `g` is, since `c ≠ 0`.
    have hg : ¬_root_.Summable g := fun hg ↦ hsum <|
      (_root_.summable_sigma_of_nonneg fun _ ↦ by positivity).mpr
        ⟨fun _ ↦ .of_finite, by simpa only [hinner] using hg.mul_left (c : ℝ)⟩
    rw [_root_.tsum_eq_zero_of_not_summable hsum, _root_.tsum_eq_zero_of_not_summable hg, _root_.MulZeroClass.mul_zero]











end NumberField.Set

end
end
