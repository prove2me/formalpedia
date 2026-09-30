-- Prove2me | solution 1 for NumberField.Set.primeIdealZetaSum_le_mul_of_encard_fiber_le
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:26.945524+00:00
-- url     : https://prove2.me/submissions/46e24454-4580-4316-a478-346a8810317b

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
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
# Counting carriers for ideals and prime ideals

Every estimate in the arithmetic-Dirichlet-series roadmap counts objects whose absolute norm does
not exceed a *real* cutoff `x`, and always inclusively: an object of norm exactly `x` is counted.
This file fixes that convention once.

The common core is Mathlib's `Northcott` property: a function `N : ι → ℕ` is Northcott when each
set `{i | N i ≤ B}` is finite.  For such an `N`:

* `TauCeti.normLE N x` is the finite set of indices with `(N i : ℝ) ≤ x`;
* `TauCeti.summatory N w x` is the inclusive sum of a weight `w` over `TauCeti.normLE N x`.

Two instances of this core carry the arithmetic content, `TauCeti.idealsLE` for the nonzero
integral ideals of `𝓞 K` and `TauCeti.primesLE` for the height-one primes, with
`TauCeti.idealSummatory`, `TauCeti.primeSummatory`, and `TauCeti.primePowerSummatory` the associated
summatory functions.  The
weighted prime counts of the roadmap are the two named specializations
`TauCeti.primeTheta`, the logarithmically weighted count, and `TauCeti.primeCount`, the
unweighted one; both are restricted to a set `S` of height-one primes through `Set.indicator`,
so no decidability hypothesis is needed on `S`.

A prime-power ideal is `𝔭 ^ k` for a unique height-one prime `𝔭` and a unique `k ≥ 1`;
`TauCeti.primePowerBase` and `TauCeti.primePowerExponent` name that pair, and
`TauCeti.idealPrimePower_eq_of_base_eq_of_exponent_eq` records that it determines the ideal.  The
exponent is `1` exactly on the primes themselves, which is `TauCeti.primePowerExponent_eq_one_iff`;
`TauCeti.IdealPrimePower.ofPrime` is the resulting inclusion of the prime carrier into the
prime-power carrier, and `TauCeti.primePowerSummatory_eq_primeSummatory` uses it to read a
prime-power sum concentrated on the exponent-one part as a sum over primes.

`TauCeti.idealsLE_filter_dvd` identifies the ideals below a cutoff divisible by a fixed nonzero
ideal `P` with the multiples of `P`, and `TauCeti.idealSummatory_ite_dvd` reads the corresponding
part of a summatory function at the rescaled cutoff `x / N(P)`.

Two lemmas move a summatory function between the three carriers.
`TauCeti.idealSummatory_eq_primePowerSummatory` reads an ideal weight vanishing off the prime
powers as a prime-power weight, and `TauCeti.idealSummatory_eq_sum_range_normFiber` regroups an
ideal summatory function into the partial sum, over `n ≤ ⌊x⌋₊`, of the total mass on the norm
fibre at `n`; `TauCeti.idealSummatory_eq_sum_Icc_normCoeff` writes the same regrouping as a
partial sum of `TauCeti.normCoeff`.  Together they present a sum over prime powers as a partial
sum of an `ArithmeticFunction`, which is the shape a Tauberian theorem consumes.

For `0 ≤ x`, a real cutoff and its floor select the same indices, so
`TauCeti.normLE_eq_normLE_natFloor` and `TauCeti.summatory_eq_summatory_natFloor` convert between
the real and natural conventions. The small-cutoff cases are degenerate for a reason worth
recording: a nonzero ideal has absolute norm at least `1`, and a height-one prime at least `2`, so
`TauCeti.idealsLE_one` isolates the unit ideal and `TauCeti.primesLE_eq_empty_of_lt_two` empties the
prime carrier below `2`.

Modifying a weight on a finite set, or a prime set on a finite symmetric difference, changes a
summatory function by a quantity that is eventually the *constant* total discrepancy; this is
`TauCeti.eventually_summatory_sub_eq` and its two prime specializations. Layer 7 uses these to
show that finite changes do not affect a density. In the same spirit,
`TauCeti.primeTheta_isLittleO_of_finite` records that a finite set of primes contributes an
eventually constant amount to `ϑ_K`, hence `o(x)`: an exceptional set can be discarded from a
counting argument outright, not merely from a density. Its `ψ` companion is
`TauCeti.primePsi_isLittleO_of_finite`.

## Roadmap role

This is Layer **4** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: the finite cutoff
carriers of 4.1, the generic summatory functions on ideals, primes, and prime powers of 4.2, and the
weighted prime counts `primeTheta` and `primeCount` of 4.3. Layer 5 supplies the actual size
estimates for these counts, and consumes the prime base and exponent of a prime-power ideal to
fibre those estimates over the primes.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters I--II.
* H. Davenport, *Multiplicative Number Theory*, Chapters 1 and 7.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

 section

namespace TauCeti

open _root_.Filter
open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain

/-! ### Ideals and height-one primes of bounded absolute norm -/



variable (K : Type*) [Field K] [NumberField K]













variable {K}

/-- The absolute norm of a nonzero integral ideal is at least `1`, as a real number. -/
theorem one_le_absNorm_real_of_nonZeroDivisors (I : (Ideal (𝓞 K))⁰) :
    (1 : ℝ) ≤ Ideal.absNorm (I : Ideal (𝓞 K)) := by
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I





/-! ### The prime base and the exponent of a prime-power ideal -/



























































variable (K)

/-! ### Summatory functions over ideals and over primes -/

































variable {K}

namespace MultiplicativeIdealWeight

variable (χ : MultiplicativeIdealWeight K)



end MultiplicativeIdealWeight

variable (K)









/-! ### The weighted prime counts -/





variable {K}
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {x : ℝ}

























































end TauCeti

end
end

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





/-- **Prime sums along a bounded fibre count.** If `π` maps `T` into `S`, does not increase
absolute norms on `T`, and every prime of `S` has at most `m` preimages in `T`, then for `s ≥ 0` the
prime sum over `T` is at most `m` times the prime sum over `S`, provided the latter converges. -/
theorem solution (hmaps : _root_.Set.MapsTo π T S)
    (hnorm : ∀ 𝔓 ∈ T, _root_.Ideal.absNorm (π 𝔓).asIdeal ≤ _root_.Ideal.absNorm 𝔓.asIdeal) {m : ℕ}
    (hfiber : ∀ 𝔭 ∈ S, (T ∩ π ⁻¹' {𝔭}).encard ≤ m) {s : ℝ} (hs : 0 ≤ s)
    (hS : _root_.Summable fun 𝔭 : S ↦ (_root_.Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :
    T.primeIdealZetaSum s ≤ m * S.primeIdealZetaSum s := by
  classical
  let f : T → S := hmaps.restrict π T S
  let g : S → ℝ := fun 𝔭 ↦ (_root_.Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)
  -- Each fibre of `f` inside a finite set of primes of `T` has at most `m` elements.
  have hcard (F : _root_.Finset T) (𝔭 : S) : (F.filter (f · = 𝔭)).card ≤ m := by
    have hsub : (((F.filter (f · = 𝔭)).map (_root_.Function.Embedding.subtype _) : _root_.Finset _) :
        _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 E))) ⊆ T ∩ π ⁻¹' {𝔭.1} := by
      simp only [_root_.Finset.coe_map, _root_.Function.Embedding.subtype_apply, _root_.Set.image_subset_iff]
      rintro 𝔓 h𝔓
      rw [_root_.Finset.mem_coe, _root_.Finset.mem_filter] at h𝔓
      exact ⟨𝔓.2, by simp [← h𝔓.2, f]⟩
    have := (_root_.Set.encard_le_encard hsub).trans (hfiber 𝔭 𝔭.2)
    rwa [_root_.Set.encard_coe_eq_coe_finsetCard, _root_.Finset.card_map, _root_.Nat.cast_le] at this
  rw [_root_.NumberField.Set.primeIdealZetaSum_def, _root_.NumberField.Set.primeIdealZetaSum_def]
  refine _root_.Real.tsum_le_of_sum_le (fun _ ↦ by positivity) fun F ↦ ?_
  calc ∑ 𝔓 ∈ F, (_root_.Ideal.absNorm 𝔓.1.asIdeal : ℝ) ^ (-s)
      ≤ ∑ 𝔓 ∈ F, g (f 𝔓) := _root_.Finset.sum_le_sum fun 𝔓 _ ↦ by
        have hpos : (0 : ℝ) < _root_.Ideal.absNorm (π 𝔓.1).asIdeal :=
          zero_lt_one.trans_le (_root_.TauCeti.one_le_absNorm_real_of_nonZeroDivisors
            ⟨_, _root_.mem_nonZeroDivisors_of_ne_zero (π 𝔓.1).ne_bot⟩)
        exact _root_.Real.rpow_le_rpow_of_nonpos hpos (by exact_mod_cast hnorm 𝔓.1 𝔓.2)
          (neg_nonpos.mpr hs)
    _ = ∑ 𝔭 ∈ F.image f, (F.filter (f · = 𝔭)).card * g 𝔭 := by
        simp only [_root_.Finset.sum_comp, _root_.nsmul_eq_mul]
    _ ≤ ∑ 𝔭 ∈ F.image f, m * g 𝔭 :=
        _root_.Finset.sum_le_sum fun 𝔭 _ ↦
          _root_.mul_le_mul_of_nonneg_right (by exact_mod_cast hcard F 𝔭) (by positivity)
    _ ≤ m * ∑' 𝔭, g 𝔭 := by
        rw [← _root_.Finset.mul_sum]
        exact _root_.mul_le_mul_of_nonneg_left (hS.sum_le_tsum _ fun _ _ ↦ by positivity)
          (by positivity)







end NumberField.Set

end
end
