-- Prove2me | solution 1 for NumberField.Chebotarev.cyclotomicArtin_surjective
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T22:16:59.193311+00:00
-- url     : https://prove2.me/submissions/d5b6751c-41a9-49c6-aa52-a9f27639bb7f

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Data_ZMod_Divisibility
import Definitions.Def_TauCeti_FieldTheory_Galois_Abelian
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Regroup
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_FrobeniusPrimeSet
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_GaloisCharacter_Cyclotomic_Basic
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_RamifiedPrimes
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_NumberTheory_NumberField_Cyclotomic_Frobenius
import Definitions.Def_TauCeti_NumberTheory_NumberField_Cyclotomic_Ramification
import Definitions.Def_TauCeti_NumberTheory_NumberField_Frobenius
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Residue
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_ArtinMap
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_Away
import Definitions.Def_TauCeti_NumberTheory_NumberField_ResidueDegree
import Definitions.Def_TauCeti_NumberTheory_NumberField_TotallyPositive
import Definitions.Def_TauCeti_NumberTheory_RamificationInertia_Tower
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Factorization
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_RamificationLocus
import Definitions.Def_TauCeti_RingTheory_Frobenius
import Definitions.Def_TauCeti_RingTheory_Ideal_Norm_AbsNorm
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.AbsoluteValue.Equivalence
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
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_NumberField_Set_HasDirichletDensity_of_symmDiff
import Theorems.Thm_NumberField_Set_hasDirichletDensity_contraction
import Theorems.Thm_NumberField_artinSymbol_map_restrictNormalHom
import Theorems.Thm_Real_neg_log_one_sub_rpow_sub_le_div
import Theorems.Thm_Real_neg_log_one_sub_sub_le
import Theorems.Thm_TauCeti_LSeriesSummable_normCoeff_one_iff
import Theorems.Thm_TauCeti_RamificationInertia_ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank
import Theorems.Thm_TauCeti_card_filter_rationalPrimeBelow_le_finrank
import Theorems.Thm_TauCeti_dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub
import Theorems.Thm_TauCeti_summable_idealTerm_of_norm_normCoeff_eq_sum_norm
import Theorems.Thm_TauCeti_tendsto_log_dedekindZeta_re_sub_log_one_div_sub_one
import Theorems.Thm_TauCeti_tsum_nat_rpow_neg_le_two

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Inversion and powers of conjugacy classes, and the size of a class

Inversion of a group is compatible with conjugacy: `x` and `y` are conjugate exactly when `x⁻¹` and
`y⁻¹` are (`TauCeti.isConj_inv_iff`). So inversion descends to the conjugacy classes, where it is an
involution, recorded here as an `InvolutiveInv (ConjClasses G)` instance; `C⁻¹` is the class of the
inverses of the members of `C`, and it has the same size as `C`. A class fixed by this involution is
a **real** class (`TauCeti.IsRealClass`).

Powering likewise commutes with conjugation, so for a **monoid** `M` it too descends to the
conjugacy classes: `ConjClasses.pow C j`, written `C ^ j`, is the class of the `j`-th powers of
the members of `C`.

The other fact collected here is that the size of a conjugacy class is the index of the centralizer
of any of its members, and so divides the order of the group: the orbit-stabilizer theorem for the
conjugation action.

## Main statements

* `TauCeti.isConj_inv_iff`: conjugacy is inherited by inverses in both directions.
* `ConjClasses.inv_mk`: the inverse of the class of `g` is the class of `g⁻¹`.
* `TauCeti.IsRealClass`: a class containing an element conjugate to its own inverse, with
  `TauCeti.isRealClass_iff_inv_eq` identifying it with being fixed by inversion.
* `ConjClasses.ncard_carrier_inv` and `ConjClasses.card_carrier_inv`: a conjugacy
  class and its inverse have the same size, in `Set.ncard` and in `Nat.card` form.
* `ConjClasses.ncard_carrier_mk` and `ConjClasses.card_carrier_mk`: the size of a
  conjugacy class is the index of the centralizer of any of its members, in `Set.ncard` and in
  `Nat.card` form.
* `ConjClasses.ncard_carrier_mk_of_mem_center`: the class of a central element is a single
  point.
* `ConjClasses.card_carrier_mul_orderOf_dvd`: the class size times the order of a member
  divides the order of the group, so the quotient below is an exact ratio.
* `ConjClasses.card_div_card_carrier_mul_orderOf_pos`: for a finite group that ratio is positive.
* `ConjClasses.card_div_card_carrier_mul_orderOf_eq_card_centralizer_div_orderOf`: that
  quotient equals the order of the centralizer divided by the order of the member.
* `ConjClasses.one_div_orderOf_div_card_div_card_carrier_mul_orderOf`: dividing `1 / orderOf σ`
  by that quotient, in a semifield of characteristic zero, leaves `#C / #G`.
* `ConjClasses.ncard_carrier_mk_eq_card_filter` and
  `ConjClasses.card_carrier_mk_eq_card_filter`: the size of a conjugacy class as the
  cardinality of a `Finset`, which makes it computable.
* `ConjClasses.card_carrier_dvd_card`: the size of a conjugacy class divides the order of
  the group, with `ConjClasses.card_carrier_cast_ne_zero` the consequence that the size of
  a class is nonzero in any semiring where the group order is, and
  `ConjClasses.card_carrier_div_card_ne_zero` the nonvanishing of `#C / #G` for a finite group.
* `ConjClasses.pow`: the power operation itself, with `C ^ j` its notation.
* `ConjClasses.mem_pow_iff`: an element lies in `C ^ j` exactly when it is a
  `j`-th power of a member of `C`, with `ConjClasses.mk_pow` the computation rule.
* `ConjClasses.pow_zero`, `ConjClasses.pow_one` and
  `ConjClasses.pow_mul`: the identity and composition laws for that power.
* `ConjClasses.map_mk`: the computation rule for `ConjClasses.map` on representatives,
  with `ConjClasses.map_pow` the consequence that the power is natural in the monoid.
* `ConjClasses.mk_ne_mk_of_orderOf_ne`: elements of different orders lie in different conjugacy
  classes.

## Implementation notes

The inversion is an instance rather than a plain function so that the notation `C⁻¹`, the
involutivity lemma `inv_inv` and the reindexing equivalence `Equiv.inv` are all available for
conjugacy classes. Powering is instead a named definition `ConjClasses.pow` with a `Pow` instance
delegating to it, so that the roadmap's `C.pow j` and the notation `C ^ j` are the same function;
the lemmas below are all stated in the `^` form. There is still no
multiplication on `ConjClasses M` — `Pow (ConjClasses M) ℕ` is a bare power operation, not the
`npow` field of a monoid structure, and none of the lemmas here presuppose one.

The power operation is developed for the Chebotarev roadmap (`Chebotarev/README.md` Layer 1,
"consumed Frobenius classes and powers of conjugacy classes", whose `Suggested.lean` pins these
signatures); its consumer there is the von Mangoldt fibre, which sums over the classes `C ^ j`.
That is also why a `pow_two_cyclicFour` regression is kept: a group of
exponent two has no proper nonidentity square, so it cannot separate a correct power operation
from one that collapses to the identity. It is `private`, being a check on this development
rather than reusable conjugacy-class API. This operation is *not* adapted from the
Birkbeck–Brasca `chebotarev-density` development, which works with `ConjClasses.mk` and
`Subgroup.zpowers` directly and never forms `C ^ j`.

The two arithmetic statements concern the quotient `#G / (#C * orderOf σ)`. The first says the
division is exact — `#C` is the index of the centralizer of `σ`, and `orderOf σ` divides that
centralizer's order, so their product divides `#G` — and the second evaluates the quotient as the
centralizer's order over `orderOf σ`. Neither asserts that either side counts anything; a caller
wanting a cardinality interpretation must supply it.
-/

 section

namespace TauCeti

variable {G : Type*} [Group G]





end TauCeti

namespace ConjClasses

variable {G : Type*} [Group G]



























end ConjClasses

namespace TauCeti

variable {G : Type*} [Group G]





-- Not a `simp` lemma: `isRealClass_iff_inv_eq` and `ConjClasses.inv_mk` already rewrite the
-- left-hand side to `ConjClasses.mk g⁻¹ = ConjClasses.mk g`, so tagging it makes `simpNF` fail.


end TauCeti

/-! ### The size of a class against the order of a member -/

namespace ConjClasses

-- Source. Both statements are specified by the Chebotarev roadmap. The divisibility is the
-- declaration pinned at `TauCetiRoadmap/Chebotarev/Suggested.lean` lines 377-382, there stated
-- with `[Finite G]`. The quotient identity is `TauCetiRoadmap/Chebotarev/README.md` §8.2, which
-- writes it `#G / (#C * f) = #Centralizer_G(σ) / f` for `f = orderOf σ` and asks for
-- `#C * f ∣ #G` as a separate statement.









end ConjClasses

/-! ### Powers of a conjugacy class -/

namespace ConjClasses

variable {M : Type*} [Monoid M]















/-- The image of the class of `a` under `ConjClasses.map f` is the class of `f a`. -/
-- Mathlib defines `ConjClasses.map` as a `Quotient.lift` and provides no computation rule for it,
-- so this reduction is stated here once and every naturality statement below rewrites with it.
@[simp]
theorem map_mk {N : Type*} [Monoid N] (f : M →* N) (a : M) :
    ConjClasses.map f (ConjClasses.mk a) = ConjClasses.mk (f a) := rfl







end ConjClasses

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
# Elementary bounds on real powers with a negative exponent

A base at least `2` raised to a negative exponent of size at least `1` is at most `1 / 2`. This
is the shape in which the local ratio of an Euler factor is bounded away from `1`, so that the
denominator `1 - y ^ (-s)` stays bounded below.

## Main results

* `Real.rpow_neg_le_half`: `y ^ (-s) ≤ 1 / 2` for `2 ≤ y` and `1 ≤ s`.
-/

 section

namespace Real

/-- If `2 ≤ y` and `1 ≤ s`, then `y ^ (-s) ≤ 1 / 2`. -/
theorem rpow_neg_le_half {y s : ℝ} (hy : 2 ≤ y) (hs : 1 ≤ s) : y ^ (-s) ≤ 1 / 2 :=
  calc y ^ (-s) ≤ (2 : ℝ) ^ (-s) := rpow_le_rpow_of_nonpos two_pos hy (by linarith)
    _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := rpow_le_rpow_of_exponent_le one_le_two (by linarith)
    _ = 1 / 2 := by norm_num

end Real

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
# Elementary bounds on `-log (1 - x)`

This file bounds the quadratic remainder `-log (1 - x) - x`, then specializes the estimate to
`x = y ^ (-s)`. The sharp factor `2` in the denominator comes from reading Mathlib's complex
logarithm bound along the reals. It also records the coarser estimate
`-log (1 - x) ≤ x + 2 x ^ 2` for `0 ≤ x ≤ 1/2`.

## Main results

* `Real.neg_log_one_sub_sub_le`: for `0 ≤ x < 1`, the remainder is at most
  `x² / (2 (1 - x))`.
* `Real.neg_log_one_sub_rpow_sub_le_div`: for `2 ≤ y` and `0 < s`, it is at most
  `y ^ (-2s) / (2 (1 - 2 ^ (-s)))`.
* `Real.neg_log_one_sub_rpow_sub_le`: for `2 ≤ y` and `1 ≤ s`, it is at most `y⁻²`.
* `Real.neg_log_one_sub_le_add_two_mul_sq`: for `0 ≤ x ≤ 1/2`, `-log (1 - x)` is at most
  `x + 2 x ^ 2`.
* `Complex.norm_neg_log_one_sub_sub_le`: for complex `z` with `‖z‖ ≤ 1/2`, the remainder
  `-log (1 - z) - z` has norm at most `‖z‖ ^ 2`.

## References

The shape of `Real.neg_log_one_sub_sub_le` follows the private declaration
`neg_log_one_sub_sub_le` in `CebotarevDensity/Density.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
C. Birkbeck and R. Brasca), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. The sharper
constant here comes from Mathlib's `Complex.norm_log_one_sub_inv_sub_self_le`.
-/

 section

namespace Real

/-- The quadratic remainder of `-log (1 - x)` is nonnegative for `x < 1`. -/
theorem neg_log_one_sub_sub_nonneg {x : ℝ} (hx1 : x < 1) :
    0 ≤ -log (1 - x) - x := by
  linarith [log_le_sub_one_of_pos (sub_pos.mpr hx1)]



/-- For `1 < y` and `0 < s`, the quadratic remainder of `-log (1 - y ^ (-s))` is
nonnegative. -/
theorem neg_log_one_sub_rpow_sub_nonneg {y s : ℝ} (hy : 1 < y) (hs : 0 < s) :
    0 ≤ -log (1 - y ^ (-s)) - y ^ (-s) :=
  neg_log_one_sub_sub_nonneg (rpow_lt_one_of_one_lt_of_neg hy (by linarith))



/-- For `2 ≤ y` and `1 ≤ s`, the quadratic remainder of `-log (1 - y ^ (-s))` is at most
`y⁻²`. -/
theorem neg_log_one_sub_rpow_sub_le {y s : ℝ} (hy : 2 ≤ y) (hs : 1 ≤ s) :
    -log (1 - y ^ (-s)) - y ^ (-s) ≤ y ^ (-(2 : ℝ)) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hxhalf : y ^ (-s) ≤ 1 / 2 := rpow_neg_le_half hy hs
  calc
    -log (1 - y ^ (-s)) - y ^ (-s) ≤ (y ^ (-s)) ^ 2 / (2 * (1 - y ^ (-s))) :=
      neg_log_one_sub_sub_le (rpow_nonneg hy0.le _) (by linarith)
    _ ≤ (y ^ (-s)) ^ 2 := div_le_self (sq_nonneg _) (by linarith)
    _ = y ^ (-(2 * s)) := by rw [pow_two, ← rpow_add hy0, ← two_mul, mul_neg]
    _ ≤ y ^ (-(2 : ℝ)) := rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- For `0 ≤ x ≤ 1/2`, `-log (1 - x) ≤ x + 2 x ^ 2`. -/
theorem neg_log_one_sub_le_add_two_mul_sq {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -log (1 - x) ≤ x + 2 * x ^ 2 := by
  -- The first-order Taylor estimate `|x + log (1 - x)| ≤ x ^ 2 / (1 - x)`.
  have h := abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_nonneg hx0]; linarith) 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero, div_one,
    abs_of_nonneg hx0] at h
  have h' : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg x]
  linarith [(abs_le.mp h).1]

end Real

namespace Complex



end Complex

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
# The divergence of `log (1 / (s - a))` as `s` decreases to `a`

`s ↦ log (1 / (s - a))` diverges to `+∞` on a right neighbourhood of `a`, for any real `a`. That
single limit is what this file provides.

The ratio statement it feeds is `TauCeti.tendsto_div_nhds_one_of_le_add_const_of_sub_const_le`,
and lives there rather than here: once a denominator diverges, any numerator agreeing with it up
to a bounded additive error gives a quotient tending to `1`. A Dirichlet density argument uses
the case `a = 1`, with a prime sum estimated as `log (1 / (s - 1)) + O(1)` as the numerator, and
reads the density off the quotient — the divergence is exactly what makes the `O(1)` immaterial.
Nothing here is specific to that application, and the file contains no number theory.

## Main results

* `Real.tendsto_log_one_div_sub_atTop` — `log (1 / (s - a))` tends to `atTop` along `𝓝[>] a`.

## References

Adapted from `tendsto_log_one_div_sub_one_atTop` in
`CebotarevDensity/ForMathlib/LogOneDivSubOne.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. The source states it at
`a = 1`; the statement here is at an arbitrary real translation point.
-/

 section

namespace Real

open Filter Topology

/-- `log (1 / (s - a))` tends to `+∞` as `s` decreases to `a`. At `a = 1` this is the divergence
driving the Dirichlet density asymptotics. -/
theorem tendsto_log_one_div_sub_atTop (a : ℝ) :
    Tendsto (fun s : ℝ ↦ Real.log (1 / (s - a))) (𝓝[>] a) atTop := by
  refine Real.tendsto_log_atTop.comp ?_
  have h1 : Tendsto (fun s : ℝ ↦ s - a) (𝓝[>] a) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_sub_right a).tendsto' a 0 (by ring)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s hs ↦ by
        simp only [Set.mem_Ioi] at hs ⊢
        linarith)
  simpa only [one_div, Pi.inv_def] using h1.inv_tendsto_nhdsGT_zero

end Real

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
# Regrouping ideal arithmetic functions by absolute norm

This file defines `TauCeti.normCoeff`, the ordinary arithmetic function obtained by summing an
`IdealArithmeticFunction` over each fibre of the absolute norm.  These fibres are finite by
`Ideal.finite_setOfPred_absNorm_eq`, so the coefficients are honest finite sums.  The resulting
function has value zero at `0`, as required by Mathlib's `ArithmeticFunction` carrier; that value
is available from `ArithmeticFunction.map_zero`.

The construction is bundled as a complex-linear map.  The basic API exposes the finite norm fibre
`TauCeti.normFiber` and its finiteness, records the value at one, proves compatibility with
complex conjugation, and records in `TauCeti.norm_normCoeff_eq_sum_norm_of_nonneg` that no
cancellation occurs inside a fibre when the values of `f` are nonnegative.  Regrouping is
compatible with transporting along an isomorphism of number fields: `TauCeti.normCoeff_map` says
that an isomorphism `e : K ≃+* L` leaves every norm coefficient unchanged.

Regrouping loses information as soon as a norm fibre has more than one element:
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg` produces a nonzero ideal arithmetic
function, with a negative value, whose norm coefficients all vanish.  This is the rejection test
that forbids weakening the nonnegativity hypothesis of the converse regrouping theorem to
nonnegativity of the coefficients themselves.

## Roadmap role

This is the finite-norm-fibre part of Layer **1.1** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  The next layer step uses these coefficients
to regroup an absolutely convergent series over nonzero ideals into a Mathlib `LSeries`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.NumberField _root_.ComplexOrder

variable (K : Type*) [Field K] [NumberField K]







/-- The absolute-norm fibre, viewed as a set, is the preimage of `{n}` under the absolute norm. -/
theorem coe_normFiber (n : ℕ) :
    (normFiber K n : Set ((Ideal (𝓞 K))⁰))
      = (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n} := by
  ext I
  simp







/-- The value of `normCoeff f` is the finite sum of `f` over the corresponding absolute-norm
fibre. -/
theorem normCoeff_apply (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f n =
      ∑ᶠ I ∈ {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n}, f I :=
  (rfl)

/-- The value of `normCoeff f` as a sum over the finite absolute-norm fibre. -/
theorem normCoeff_eq_sum_normFiber (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f n = ∑ I ∈ normFiber K n, f I := by
  rw [normCoeff_apply, finsum_mem_eq_finite_toFinset_sum _ (finite_normFiber K n)]
  simp only [normFiber]













/-- **Absence of cancellation inside norm fibres**, for a nonnegative ideal arithmetic function:
the absolute value of a norm coefficient is the sum of the absolute values over the fibre. -/
theorem norm_normCoeff_eq_sum_norm_of_nonneg (f : IdealArithmeticFunction K) (hf : ∀ I, 0 ≤ f I)
    (n : ℕ) : ‖normCoeff K f n‖ = ∑ I ∈ normFiber K n, ‖f I‖ := by
  have h : normCoeff K f n = ((∑ I ∈ normFiber K n, ‖f I‖ : ℝ) : ℂ) := by
    rw [normCoeff_eq_sum_normFiber]
    push_cast
    exact Finset.sum_congr rfl fun I _ ↦ Complex.eq_coe_norm_of_nonneg (hf I)
  rw [h, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]

/-! ### The cancellation rejection test -/



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
# Regrouping an ideal-indexed Dirichlet series by absolute norm

An `TauCeti.IdealArithmeticFunction K` has two Dirichlet series attached to it: the series indexed
by the nonzero integral ideals of `𝓞 K`, whose terms are `TauCeti.idealTerm`, and the Mathlib
`LSeries` of the regrouped coefficients `TauCeti.normCoeff`. This file proves that the second is
obtained from the first by summing over the finite absolute-norm fibres, so that absolute
convergence of the ideal-indexed series transfers to the `LSeries` together with the value of the
sum.

## Main definitions

* `TauCeti.idealTerm f s I` is the term `f I / N(I) ^ s` of the ideal-indexed Dirichlet series.
* `TauCeti.idealAbscissaOfAbsConv f` is the abscissa of absolute convergence of that series, the
  ideal-indexed analogue of Mathlib's `LSeries.abscissaOfAbsConv`.

## Main results

* `TauCeti.regroupByNorm`: if the ideal-indexed series has sum `L` at `s`, then so does the
  `LSeries` of `TauCeti.normCoeff f`; `TauCeti.LSeriesSummable_normCoeff` and
  `TauCeti.LSeries_normCoeff` are the summability and value statements it packages.
* `TauCeti.summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`: weighting the ideal terms
  by `log N(I)` keeps them summable strictly to the right of a point of absolute convergence.
* `TauCeti.abscissaOfAbsConv_normCoeff_le`: consequently the grouped abscissa of absolute
  convergence is at most the ideal-indexed one.
* `TauCeti.summable_idealTerm_of_norm_normCoeff_eq_sum_norm`: the converse holds whenever no
  cancellation occurs inside a norm fibre. `TauCeti.summable_idealTerm_of_nonneg` and
  `TauCeti.idealAbscissaOfAbsConv_eq_abscissaOfAbsConv` specialize it to the case where every
  *individual ideal summand* is nonnegative, where moreover the two abscissae agree.

## Implementation notes

The regrouping is an instance of Mathlib's `HasSum.tsum_fiberwise` along the absolute norm
`fun I ↦ Ideal.absNorm (I : Ideal (𝓞 K))`, whose fibres are the finite sets
`TauCeti.normFiber K n`. Absolute convergence of the ideal-indexed series is expressed as plain
`Summable`, which for a complex-valued family is unconditional convergence and hence absolute
convergence; no rearrangement hypothesis is therefore needed for the transfer.

The converse is proved through `summable_partition` applied to the norms of the terms. All it
needs about `f` is that the norm of each grouped coefficient is the sum of the norms over its
fibre — the absence of cancellation inside the fibre. Nonnegativity of every ideal summand is one
way to secure that, through `TauCeti.norm_normCoeff_eq_sum_norm_of_nonneg`; it is the step that
fails under cancellation, as the rejection test
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg` records. That test is a statement about
`TauCeti.normCoeff` alone, so it lives with that definition rather than here.

## Roadmap role

This is Layer **1.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`; the required worked
example 9 accompanies it in `TauCeti/NumberTheory/ArithmeticDirichletSeries/NormCoeff.lean`. The
exact value of the abscissa for the trivial weight is deliberately not proved here: its divergence
input is the Layer 5 ideal count of
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Estimates.lean`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.NumberField _root_.ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

/-! ### The ideal-indexed term -/



/-- Defining equation of `TauCeti.idealTerm`. -/
theorem idealTerm_def (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    idealTerm K f s I = f I / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s :=
  (rfl)

/-- The absolute value of an ideal term depends on `s` only through its real part. -/
@[simp]
theorem norm_idealTerm (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    ‖idealTerm K f s I‖ = ‖f I‖ / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s.re := by
  rw [idealTerm_def, norm_div,
    Complex.norm_natCast_cpow_of_pos (Ideal.absNorm_pos_of_nonZeroDivisors I)]









/-! ### Regrouping -/

/-- The `n`-th term of the regrouped `LSeries` is the finite sum of the ideal terms over the
absolute-norm fibre of `n`. -/
theorem term_normCoeff_eq_sum_normFiber (f : IdealArithmeticFunction K) (s : ℂ) (n : ℕ) :
    LSeries.term (normCoeff K f) s n = ∑ I ∈ normFiber K n, idealTerm K f s I := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, normCoeff_eq_sum_normFiber, Finset.sum_div]
  refine Finset.sum_congr rfl fun I hI ↦ ?_
  rw [idealTerm_def, (mem_normFiber K).mp hI]

/-- The regrouped `LSeries` terms as the fibrewise sums of the ideal terms along the absolute
norm. This is the form consumed by `HasSum.tsum_fiberwise`; `term_normCoeff_eq_sum_normFiber` is
the usable finite-fibre formula. -/
private theorem term_normCoeff (f : IdealArithmeticFunction K) (s : ℂ) :
    LSeries.term (normCoeff K f) s = fun n ↦
      ∑' I : (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n},
        idealTerm K f s I := by
  funext n
  rw [← coe_normFiber, Finset.tsum_subtype' (normFiber K n) (idealTerm K f s)]
  exact term_normCoeff_eq_sum_normFiber K f s n

/-- **Regrouping by absolute norm.** If the Dirichlet series indexed by the nonzero integral ideals
converges absolutely at `s` with sum `L`, then the Mathlib `LSeries` of the regrouped coefficients
`TauCeti.normCoeff f` converges absolutely at `s` with the same sum.

Absolute convergence of the ideal-indexed series is the hypothesis `HasSum`, which for a
complex-valued family is unconditional. No hypothesis on the individual ideal summands is needed;
compare `TauCeti.summable_idealTerm_of_nonneg` for the converse, which does need one. -/
theorem regroupByNorm {f : IdealArithmeticFunction K} {s L : ℂ} (h : HasSum (idealTerm K f s) L) :
    LSeriesHasSum (normCoeff K f) s L := by
  simpa only [LSeriesHasSum, term_normCoeff] using
    h.tsum_fiberwise fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))

/-- Absolute convergence of the ideal-indexed Dirichlet series implies that of the regrouped
`LSeries`. -/
theorem LSeriesSummable_normCoeff {f : IdealArithmeticFunction K} {s : ℂ}
    (h : Summable (idealTerm K f s)) : LSeriesSummable (normCoeff K f) s :=
  LSeriesHasSum.LSeriesSummable (regroupByNorm K h.hasSum)



/-! ### The ideal-indexed abscissa of absolute convergence -/













/-! ### The converse, in the absence of cancellation inside norm fibres -/







/-- **The converse regrouping, under nonnegativity of every ideal summand.** If every value of `f`
is a nonnegative real number, then absolute convergence of the regrouped `LSeries` implies absolute
convergence of the ideal-indexed series.

This is the special case of `TauCeti.summable_idealTerm_of_norm_normCoeff_eq_sum_norm` in which
nonnegativity rules out cancellation. Nonnegativity of the *grouped* coefficients
`TauCeti.normCoeff f` does not suffice; see
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg`. -/
theorem summable_idealTerm_of_nonneg (f : IdealArithmeticFunction K) (hf : ∀ I, 0 ≤ f I) {s : ℂ}
    (h : LSeriesSummable (normCoeff K f) s) : Summable (idealTerm K f s) :=
  summable_idealTerm_of_norm_normCoeff_eq_sum_norm K f
    (norm_normCoeff_eq_sum_norm_of_nonneg K f hf) h



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
# Linear ideal counts and the exact abscissa of the trivial ideal weight

Mathlib's `NumberField.Ideal.tendsto_norm_le_div_atTop₀` says that the number of nonzero integral
ideals of `𝓞 K` of absolute norm at most `x` is asymptotic to `ρ x`, with `ρ` the positive residue
of the Dedekind zeta function.  This file turns that single asymptotic into the *two-sided* linear
bounds that every later estimate of the roadmap counts against, and then spends them on the exact
abscissa of absolute convergence of the trivial ideal weight.

Both directions are needed.  Convergence uses the upper bound alone: it makes the partial sums of
the norm coefficients `O(n)`, so Mathlib's `LSeriesSummable_of_sum_norm_bigO` gives absolute
convergence on `Re s > 1`.  Divergence at `s = 1` uses both bounds together, to estimate the mass
of a block `N < n ≤ m N` of fixed ratio `m` as a difference of endpoint counts: the lower bound at
the right endpoint `m N` and the upper bound at the left endpoint `N` leave the block at least
`lower * m N - upper * N` of coefficient mass, so the terms `‖a n‖ / n` add up to at least
`lower - upper / m`, which is at least `lower / 2` once `m ≥ 2 * upper / lower`, while the blocks
of a convergent series of nonnegative terms must become arbitrarily small.

## Main definitions

* `TauCeti.IdealCountingLinearBounds K` packages positive constants `lower` and `upper` with the
  two-sided bound `lower * x ≤ #{I ≠ 0 | N(I) ≤ x} ≤ upper * x`, valid from cutoff `1` on.
* `TauCeti.card_primePowersLE_isBigO` transfers the upper ideal-count bound to the number of
  prime-power ideals at most `x`.

## Main results

* `TauCeti.idealCount_linearBounds`: such a package exists for every number field.
* `TauCeti.abscissaOfAbsConv_normCoeff_one`: the abscissa of absolute convergence of the trivial
  ideal weight is exactly `1`; `TauCeti.LSeriesSummable_normCoeff_one_iff` is the sharp
  convergence criterion.
* `TauCeti.abscissaOfAbsConv_dedekindZetaCoeff` and `TauCeti.LSeriesSummable_dedekindZetaCoeff_iff`
  are the same two statements for `TauCeti.dedekindZetaCoeff`, the coefficient system Mathlib's
  `NumberField.dedekindZeta` is the `LSeries` of.  That system counts *all* integral ideals, so it
  differs from the trivial norm coefficients at `n = 0` and the two statements are related only
  through the `n ≠ 0` congruence `LSeries.abscissaOfAbsConv_congr`.
* `TauCeti.summable_idealTerm_of_bounded_of_one_lt_re`: a uniformly bounded weight has an
  absolutely convergent ideal-indexed Dirichlet series on `Re s > 1`, and
  `TauCeti.summable_idealTerm_of_unitary_of_one_lt_re` is its unitary specialization.
* `TauCeti.idealAbscissaOfAbsConv_lt_re_of_bounded`: the same hypothesis places the ideal-indexed
  abscissa of absolute convergence strictly below every `Re s > 1`.

## Implementation notes

The counting function is Mathlib's own
`Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x}`, written out rather
than abbreviated, so that the bounds apply to `NumberField.Ideal.tendsto_norm_le_div_atTop₀`
without a translation lemma.  The inclusive real cutoff is the one fixed by the conventions table
of the roadmap.

`TauCeti.NumberTheory.EffectiveBounds.IdealCount` proves the *effective* bound
`#{I ≠ 0 | N(I) ≤ x} ≤ x² 2^[K:ℚ]`, with an explicit constant but the wrong exponent; it cannot
prove convergence at `Re s > 1`, and it has no lower bound at all.

## Relationship to other estimates

The unweighted prime-power cardinality estimate is separate from the weighted higher-prime-power
estimates in `HigherPrimePowers.lean`.  The abscissa results above depend only on the two-sided
linear ideal counts, not on the analytic continuation of the Dedekind zeta function or its pole at
`s = 1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti

open _root_.Filter
open scoped _root_.nonZeroDivisors _root_.NumberField _root_.Topology _root_.ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

/-! ### Finiteness and monotonicity of the ideal count -/







/-! ### Two-sided linear bounds -/











/-! ### Partial sums of the trivial norm coefficients -/







/-! ### The exact abscissa of the trivial ideal weight -/















/-! ### The exact abscissa, and its Dedekind zeta form -/





/-- The ideal-indexed Dirichlet series of the trivial ideal weight converges absolutely exactly on
`Re s > 1`. -/
theorem summable_idealTerm_one_iff {K : Type*} [Field K] [NumberField K] {s : ℂ} :
    Summable (idealTerm K (1 : IdealArithmeticFunction K) s) ↔ 1 < s.re := by
  refine ⟨fun h ↦ (LSeriesSummable_normCoeff_one_iff K).mp (LSeriesSummable_normCoeff K h),
    fun h ↦ ?_⟩
  exact summable_idealTerm_of_nonneg K 1 (fun _ ↦ zero_le_one)
    ((LSeriesSummable_normCoeff_one_iff K).mpr h)











end TauCeti

end
end

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Convergence of the ideal- and prime-indexed Dirichlet series

The nonzero integral ideals of `𝓞 K` carry the Dirichlet series `∑ N(I) ^ (-s)`, whose abscissa
of absolute convergence is exactly `1`: that is `TauCeti.summable_idealTerm_one_iff`, read off
from the two-sided linear ideal counts.  Distinct height-one primes are distinct nonzero
integral ideals, so the prime-indexed series `∑ N(𝔭) ^ (-s)` is a subfamily of that one, and
converges for every `s > 1`.  Only convergence transfers this way, not the abscissa: divergence
of the all-prime sum at `s = 1` is a separate statement, and is not proved here.

`NumberField.Set.primeIdealZetaSum S s` is that sum restricted to a set `S` of primes.  It is a
`tsum`, and a `tsum` takes the junk value `0` on a family that is not summable, so summability
is what separates a statement about the prime Dirichlet sum from a statement about that junk
value.  The results below supply it for every `s > 1` and every set of primes.

## Main results

* `TauCeti.summable_absNorm_rpow_ideal_iff`: over the nonzero integral ideals of `𝓞 K`, the
  series `∑ N(I) ^ (-s)` converges exactly for `1 < s`.  This is the real-variable form of
  `TauCeti.summable_idealTerm_one_iff`.
* `TauCeti.summable_absNorm_rpow_primes_of_one_lt`: over the height-one primes of `𝓞 K`, the
  series `∑ N(𝔭) ^ (-s)` converges for every `1 < s`.
* `TauCeti.summable_absNorm_rpow_subtype_of_one_lt`: the same over an arbitrary set of
  height-one primes.  This is the family `NumberField.Set.primeIdealZetaSum` sums, so it is the
  form its consumers need.
* `NumberField.Set.primeIdealZetaSum_univ`: the prime ideal zeta sum over all height-one primes as
  a sum over the whole height-one spectrum.
* `NumberField.Set.primeIdealZetaSum_mono_set`: the prime ideal zeta sum is monotone under
  inclusion of sets of primes, given summability over the larger set;
  `NumberField.Set.primeIdealZetaSum_mono_set_of_one_lt` is its `1 < s` specialization.
* `NumberField.Set.primeIdealZetaSum_pos`: a summable sum over a nonempty set of primes is
  positive; `NumberField.Set.primeIdealZetaSum_univ_pos` applies this to all primes. The
  corresponding `_of_one_lt` lemmas supply summability from `1 < s`.

## Implementation notes

The prime-indexed statement is obtained by restricting the ideal-indexed one along
`𝔭 ↦ 𝔭.asIdeal`, which is injective into `(Ideal (𝓞 K))⁰`, rather than by comparing each
`N(𝔭) = p ^ f` with the rational prime `p` below it and summing over the rational primes.  The
restriction is the shorter route on the full set of primes, and reuses the exact abscissa already
established for the trivial ideal weight.  The comparison route is not redundant: on the primes
of residue degree above one it yields the strictly wider half-line `s > 1/2`, and
`TauCeti.summable_absNorm_rpow_higherDegreePrimes` takes it for exactly that reason.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* Adapted from the Birkbeck–Brasca Chebotarev density project,
  <https://github.com/CBirkbeck/chebotarev-density> (Apache-2.0), commit
  `8575c9df1ae0a61120ab5c964c7911414254bec7`, file `CebotarevDensity/Density.lean`:
  `summable_absNorm_rpow_ideal_iff` from `summable_nonzeroIdeal_absNorm_rpow`,
  `summable_absNorm_rpow_subtype_of_one_lt` from `summable_prime_absNorm_rpow`, and
  `NumberField.Set.primeIdealZetaSum_mono_set` from `primeIdealZetaSum_le_of_subset`.
-/

 section

open _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.nonZeroDivisors _root_.NumberField

variable {K : Type*} [Field K] [NumberField K]

namespace TauCeti


/-! ### The ideal-indexed series, as a real Dirichlet series -/

/-- **The ideal-indexed Dirichlet series converges exactly on `s > 1`.** The real-variable form
of `TauCeti.summable_idealTerm_one_iff`, stated for the real power `N(I) ^ (-s)` rather than for
the complex term `TauCeti.idealTerm`, which is the shape the prime-indexed results below meet. -/
@[simp]
theorem summable_absNorm_rpow_ideal_iff {s : ℝ} :
    (Summable fun I : (Ideal (𝓞 K))⁰ ↦ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s)) ↔ 1 < s := by
  -- Each real term is the norm of the complex term at `s`, and norms decide summability.
  have key : (fun I : (Ideal (𝓞 K))⁰ ↦ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s))
      = fun I ↦ ‖idealTerm K (1 : IdealArithmeticFunction K) (s : ℂ) I‖ :=
    funext fun I ↦ by simp [Real.rpow_neg]
  rw [key, summable_norm_iff, summable_idealTerm_one_iff, Complex.ofReal_re]

/-! ### The prime-indexed series -/

/-- **The prime-indexed Dirichlet series converges for `s > 1`.** The height-one-prime analogue of
`TauCeti.summable_absNorm_rpow_ideal_iff`. -/
theorem summable_absNorm_rpow_primes_of_one_lt {s : ℝ} (hs : 1 < s) :
    Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
  -- Every height-one prime is a nonzero integral ideal and is determined by that ideal, so the
  -- prime-indexed family is an injective reindexing of a subfamily of the ideal-indexed one.
  -- The injectivity is Mathlib's `HeightOneSpectrum.asIdeal_injective` factored through the
  -- `nonZeroDivisors` coercion; nothing about it is proved here.
  have hinj : Function.Injective fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      (⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩ : (Ideal (𝓞 K))⁰) :=
    Function.Injective.of_comp (f := Subtype.val) HeightOneSpectrum.asIdeal_injective
  exact ((summable_absNorm_rpow_ideal_iff.mpr hs).comp_injective hinj).congr fun _ ↦ rfl

/-- **Restricted to any set of height-one primes**, the prime-indexed Dirichlet series still
converges for `s > 1`: a subfamily of a summable family is summable.

This is the family `NumberField.Set.primeIdealZetaSum` sums, so it is the summability its
consumers need in order to denote a genuine sum rather than the `tsum` junk value. -/
theorem summable_absNorm_rpow_subtype_of_one_lt (S : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ}
    (hs : 1 < s) : Summable fun 𝔭 : S ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) :=
  (summable_absNorm_rpow_primes_of_one_lt hs).subtype S

end TauCeti

namespace NumberField.Set

open _root_.TauCeti

/-- The prime ideal zeta sum over all height-one primes is the sum over the whole height-one
spectrum. -/
@[simp]
theorem primeIdealZetaSum_univ (s : ℝ) :
    (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s =
      ∑' P : HeightOneSpectrum (𝓞 K), (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) := by
  rw [primeIdealZetaSum_def,
    tsum_univ fun P : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)]





/-- **A summable prime ideal zeta sum over a nonempty set of primes is positive.** Every term is
positive; summability ensures that the sum is genuine rather than the `tsum` junk value `0`. -/
theorem primeIdealZetaSum_pos {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Nonempty) {s : ℝ}
    (h : Summable fun 𝔭 : S ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :
    0 < S.primeIdealZetaSum s := by
  obtain ⟨𝔭, h𝔭⟩ := hS
  rw [primeIdealZetaSum_def]
  exact h.tsum_pos (fun _ ↦ by positivity) ⟨𝔭, h𝔭⟩
    (Real.rpow_pos_of_pos (Nat.cast_pos.2 (Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨_, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩)) _)



/-- **A summable sum over all primes is positive.** This is the denominator of the ratio defining
`NumberField.Set.HasDirichletDensity`; the ring of integers is not a field, so it has a height-one
prime. -/
theorem primeIdealZetaSum_univ_pos {s : ℝ}
    (h : Summable fun 𝔭 : (Set.univ : Set (HeightOneSpectrum (𝓞 K))) ↦
      (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :
    0 < (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s := by
  obtain ⟨𝔭, -⟩ := (HeightOneSpectrum.ideal_ne_top_iff_exists
    (RingOfIntegers.not_isField K) (⊥ : Ideal (𝓞 K))).1 bot_ne_top
  exact primeIdealZetaSum_pos ⟨𝔭, Set.mem_univ 𝔭⟩ h

/-- The `1 < s` specialization of `primeIdealZetaSum_univ_pos`, where summability is automatic. -/
theorem primeIdealZetaSum_univ_pos_of_one_lt {s : ℝ} (hs : 1 < s) :
    0 < (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s :=
  primeIdealZetaSum_univ_pos (summable_absNorm_rpow_subtype_of_one_lt Set.univ hs)

end NumberField.Set

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
# One-sided bounds for Dirichlet density

For a set `S` of nonzero prime ideals of a number field, Mathlib's
`NumberField.Set.HasDirichletDensity S δ` says that the ratio

`S.primeIdealZetaSum s / Set.univ.primeIdealZetaSum s`

tends to `δ` as `s` approaches `1` from the right.  Squeeze arguments often produce the two
sides of this limit separately.  This file records those one-sided conclusions as
`NumberField.Set.IsLowerDirichletDensityBound S δ` and
`NumberField.Set.IsUpperDirichletDensityBound S δ`.

The predicates use eventual epsilon inequalities, rather than assigning junk-valued lower and
upper densities.  They are monotone in the proposed bound, and a common lower and upper bound
forces a Dirichlet density.  A lower bound is always at most an upper bound; this
comparison also gives the natural interval restrictions on one-sided bounds.

## Main results

* `NumberField.Set.hasDirichletDensity_iff`: Mathlib's `HasDirichletDensity`, unfolded to the
  convergence of the defining ratio.
* `NumberField.Set.HasDirichletDensity.isLowerDirichletDensityBound` and
  `NumberField.Set.HasDirichletDensity.isUpperDirichletDensityBound`: a Dirichlet density is
  both a lower and an upper bound.
* `NumberField.Set.isLowerDirichletDensityBound_of_forall_lt` and
  `NumberField.Set.isUpperDirichletDensityBound_of_forall_gt`: a value is a lower (upper) bound as
  soon as every smaller (larger) value is.
* `NumberField.Set.IsLowerDirichletDensityBound.le_of_isUpperDirichletDensityBound`:
  every lower bound is at most every upper bound.
* `NumberField.Set.hasDirichletDensity_of_upperBound_of_lowerBound`: matching one-sided bounds
  force a Dirichlet density.
* `NumberField.Set.hasDirichletDensity_iff_bounds`: the resulting characterization of
  Dirichlet density.

## References

* J.-P. Serre, *Corps locaux*, Chapter VI.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

 section

open _root_.Filter _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.Topology

namespace NumberField.Set

variable {K : Type*} [Field K] [NumberField K]

/-- Unfolds `HasDirichletDensity S δ` to the convergence, as `s → 1⁺`, of the ratio of the
partial prime sum over `S` to the sum over all primes. -/
theorem hasDirichletDensity_iff {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ} :
    S.HasDirichletDensity δ ↔
      Tendsto (fun s : ℝ ↦ S.primeIdealZetaSum s /
        NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s)
        (𝓝[>] 1) (𝓝 δ) :=
  Iff.rfl











-- The proof below follows `NumberField.Set.HasDirichletDensity.le_one` from
-- `Mathlib.NumberTheory.NumberField.DirichletDensity`.




























end NumberField.Set

end
end

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The Boolean calculus of Dirichlet density

For a number field `K`, Mathlib's `NumberField.Set.HasDirichletDensity S δ` says that

`S.primeIdealZetaSum s / Set.univ.primeIdealZetaSum s → δ` as `s → 1⁺`.

This file proves the elementary calculus of this predicate: uniqueness, the value `1` on all
primes, monotonicity, additivity on finite disjoint unions, complements, and two squeezes. The first
squeezes a set between two sets of the same density. The second is the finite-partition squeeze:
given a finite pairwise disjoint family whose union has `δ` as an *upper* density bound, lower
bounds on every member that already sum to `δ` leave no room, so each member's density is exactly
its bound. It also shows that one-sided density bounds move along inclusions of sets, which is
what makes the first squeeze work; the second rests instead on splitting the union's ratio exactly
and spending the summed lower bounds against it.

All of these are statements about the ratio for `s` close to `1` from the right, and on that
side both inputs they need are available: for `1 < s` each partial sum is a genuine sum rather
than the `tsum` junk value (`TauCeti.summable_absNorm_rpow_subtype_of_one_lt`), and the all-prime
denominator is positive (`NumberField.Set.primeIdealZetaSum_univ_pos_of_one_lt`). In particular
nothing here uses the divergence of the all-prime sum at `s = 1`. That divergence is what makes a
finite set of primes have density zero; the finite-error statements that use it are in
`TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Negligible`.

## Main results

* `NumberField.Set.hasDirichletDensity_univ`: all primes have Dirichlet density `1`.
* `NumberField.Set.HasDirichletDensity.mono`: inclusion of prime sets orders their densities.
* `NumberField.Set.HasDirichletDensity.union` and
  `NumberField.Set.hasDirichletDensity_biUnion_finset`: Dirichlet density is additive on finite
  disjoint unions.
* `NumberField.Set.HasDirichletDensity.compl`: the complement of a set of density `δ` has
  density `1 - δ`.
* `NumberField.Set.IsLowerDirichletDensityBound.mono_set` and
  `NumberField.Set.IsUpperDirichletDensityBound.mono_set`: lower bounds pass to supersets and
  upper bounds to subsets.
* `NumberField.Set.hasDirichletDensity_of_subset_of_subset`: a set squeezed between two sets of
  density `δ` has density `δ`.
* `NumberField.Set.isUpperDirichletDensityBound_of_forall_isLowerDirichletDensityBound`: in a
  finite disjoint family whose union has `δ` as an upper density bound, lower bounds summing to
  `δ` bound each member from above as well.
* `NumberField.Set.hasDirichletDensity_of_squeeze`: hence each such
  member has density exactly its lower bound.

## References

* The declarations and proof structure are adapted from the `HasNaturalDensity` calculus in
  `TauCeti.NumberTheory.ArithmeticDirichletSeries.NaturalDensity`.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.1.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* The finite-partition squeeze is adapted from C. Birkbeck,
  [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/Abelian.lean`, whose
  `tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one` and `ratioSum_frobeniusFibres_tendsto_one`
  are the corresponding steps: the member-sum identity divided by the all-prime sum, and the
  `#s * ε` budget that turns the other members' lower bounds into this one's upper bound.
-/

 section

namespace NumberField.Set

open _root_.Filter _root_.IsDedekindDomain _root_.NumberField _root_.TauCeti
open scoped _root_.NumberField _root_.Topology

variable {K : Type*} [Field K] [NumberField K]
variable {S T U : Set (HeightOneSpectrum (𝓞 K))} {δ ε : ℝ}

/-- A set of prime ideals has at most one Dirichlet density. -/
theorem HasDirichletDensity.unique (hδ : HasDirichletDensity S δ)
    (hε : HasDirichletDensity S ε) : δ = ε :=
  tendsto_nhds_unique (hasDirichletDensity_iff.1 hδ) (hasDirichletDensity_iff.1 hε)

/-- The set of all prime ideals has Dirichlet density one. -/
@[simp]
theorem hasDirichletDensity_univ :
    HasDirichletDensity (Set.univ : Set (HeightOneSpectrum (𝓞 K))) 1 := by
  refine hasDirichletDensity_iff.2 <| tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  exact (div_self (primeIdealZetaSum_univ_pos_of_one_lt hs).ne').symm

























end NumberField.Set

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
# Ramification and inertia counting criteria

This file records Galois consequences of the fundamental identity for primes in finite
extensions of domains. First, in a Galois extension the number of primes above a prime ideal is
maximal exactly when the common ramification index and inertia degree are both `1`. Second, the
cardinality of the inertia subgroup of a prime `P` upstairs is the ramification index of `P`
itself over the base, rather than the `Ideal.ramificationIdxIn` of the prime below it.

The rest of the file is about how inertia subgroups vary with the prime. Translating a prime by
`σ` conjugates its inertia subgroup by `σ`, since `τ • x - x ∈ σ • P` says exactly
`(σ⁻¹ τ σ) • y - y ∈ P` after the substitution `x = σ • y`. Because the Galois group acts
transitively on the primes above a fixed prime of the base, a *commutative* Galois group therefore
has one inertia subgroup per prime of the base, not one per prime upstairs. That uniformity is
what lets a statement about ramification in an intermediate field be tested at a single prime
upstairs.

## Main results

* `TauCeti.RamificationInertia.ncard_primesOver_eq_natCard_iff_of_isGaloisGroup`:
  the domain/flat Galois counting criterion.
* `Ideal.card_inertia_eq_ramificationIdx`: the un-`In` form of the inertia count.
* `Ideal.mem_inertia_pointwise_smul_iff`: translation conjugates inertia subgroups.
* `Ideal.inertia_pointwise_smul`: for a commutative Galois group, translation leaves the inertia
  subgroup unchanged.
* `Ideal.inertia_eq_of_liesOver`: for a commutative Galois group, all the primes above a fixed
  prime of the base have the same inertia subgroup.
* `Ideal.isUnramifiedAt_pointwise_smul_iff`: unramifiedness is invariant under translation by
  an algebra automorphism.
* `Ideal.isUnramifiedAt_of_isUnramifiedAt_of_isGaloisGroup`: unramifiedness transfers between
  primes above the same base prime in a Galois extension.

## Provenance

Built directly on Mathlib's unramifiedness transport
(`AlgEquiv.isUnramifiedAt_of_eq_comap`), on its Galois fundamental identity
(`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`), on its inertia count
(`Ideal.card_inertia_eq_ramificationIdxIn`), and on its transitivity statement
(`Ideal.exists_smul_eq_of_isGaloisGroup`).
-/

 section

open Ideal Module

namespace Ideal

open scoped Pointwise

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]





end Ideal

namespace Ideal

/-- The cardinality of the inertia subgroup of `P` is the ramification index of `P` over `R`.
This is `Ideal.card_inertia_eq_ramificationIdxIn` stated with the ramification index of `P`
itself rather than with `Ideal.ramificationIdxIn` of the ideal below it. -/
theorem card_inertia_eq_ramificationIdx (R : Type*) {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsDomain R] [IsDomain S] [Module.Finite R S] [Module.Flat R S] (G : Type*)
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S] (P : Ideal S) [P.IsPrime]
    [PerfectField (P.under R).ResidueField] :
    Nat.card (P.inertia G) = P.ramificationIdx R :=
  (card_inertia_eq_ramificationIdxIn (G := G) (P.under R) P).trans
    (ramificationIdxIn_eq_ramificationIdx (P.under R) P G)

end Ideal

namespace TauCeti.RamificationInertia

/-- In a finite flat Galois extension of domains, the number of primes over a prime ideal
equals the order of the Galois group iff the common ramification index and inertia degree are
both `1`. -/
theorem ncard_primesOver_eq_natCard_iff_of_isGaloisGroup {A B : Type*}
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    [Module.Flat A B] (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] (P : Ideal A) [P.IsPrime] : (primesOver P B).ncard = Nat.card G ↔
      P.ramificationIdxIn B = 1 ∧ P.inertiaDegIn B = 1 := by
  have h_main := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn P B G
  have hG : 0 < Nat.card G := Nat.card_pos
  constructor
  · intro hn
    rw [hn] at h_main
    have hef : P.ramificationIdxIn B * P.inertiaDegIn B = 1 :=
      Nat.eq_of_mul_eq_mul_left hG (by rw [mul_one]; exact h_main)
    exact mul_eq_one.mp hef
  · rintro ⟨he, hf⟩
    simpa [he, hf] using h_main

end TauCeti.RamificationInertia

namespace Ideal

section Inertia

open scoped Pointwise

variable {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]



variable (σ : G) (P : Ideal S)



end Inertia

section InertiaOver

open scoped Pointwise

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A) (P Q : Ideal B)
  [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p] (G : Type*) [Group G] [Finite G]
  [IsMulCommutative G] [MulSemiringAction G B] [IsGaloisGroup G A B]



end InertiaOver

end Ideal

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
# The Frobenius, the inertia subgroup, and the decomposition group

Let `L / K` be a finite Galois extension of number fields with Galois group `G = Gal(L/K)`, and
let `Q` be a nonzero prime of `𝓞 L` lying over `𝔭 = Q ∩ 𝓞 K`. Mathlib's `IsArithFrobAt`
expresses that an element `σ ∈ G` satisfies `σ x ≡ x ^ #(𝓞 K ⧸ 𝔭) (mod Q)`. Tau Ceti's
`NumberField.exists_isArithFrobAt` supplies such an element, and
`NumberField.isArithFrobAt_eq_of_isUnramifiedAt` proves it unique when `L / K` is unramified at
`Q`. This file identifies what that element is. In general, a Frobenius at `Q` together with the
inertia subgroup of `Q` generates the decomposition group of `Q`; at an unramified prime the
inertia subgroup is trivial, and the Frobenius alone generates the decomposition group, mapping
to the Frobenius automorphism of the residue extension.

The link is Mathlib's `Ideal.Quotient.stabilizerHom`, the action of the decomposition group
`MulAction.stabilizer G Q` on the residue extension `(𝓞 L ⧸ Q) / (𝓞 K ⧸ 𝔭)`. Its kernel is the
inertia subgroup, which is trivial exactly when `Q` is unramified, because the cardinality of the
inertia subgroup is the ramification index (`Ideal.card_inertia_eq_ramificationIdx`). So at an
unramified prime the decomposition group embeds in the residue Galois group, and a Frobenius
element is precisely a preimage of the residue Frobenius `x ↦ x ^ #(𝓞 K ⧸ 𝔭)`. Counting through
that embedding turns the classical facts about finite fields into facts about `G`:

* the order of a Frobenius element is the inertia degree `f(Q/𝔭)`;
* the decomposition group has cardinality `f(Q/𝔭)` as well, so the embedding is an isomorphism;
* consequently the decomposition group is `⟨σ⟩`, and it is cyclic.

The last section transports these statements along the action of `G` on the primes above `𝔭`.
Unramifiedness is invariant under that action, and the Frobenius at `τ • Q` is the conjugate
`τ σ τ⁻¹`: Mathlib's `IsArithFrobAt.conj` gives one inclusion and uniqueness at the unramified
prime `τ • Q` gives the other.

## Main results

* `Ideal.isUnramifiedAt_iff_inertia_eq_bot`: unramifiedness at `Q` is triviality of the
  inertia subgroup of `Q` in `Gal(L/K)`.
* `Ideal.stabilizerHom_eq_frobeniusAlgEquivOfAlgebraic`: a Frobenius element at `Q` acts on
  the residue field `𝓞 L ⧸ Q` as the residue Frobenius.
* `Ideal.orderOf_eq_inertiaDeg_of_isArithFrobAt`: a Frobenius element at an unramified `Q`
  has order the inertia degree of `Q` over `𝓞 K`.
* `Ideal.zpowers_eq_stabilizer_of_isArithFrobAt`: a Frobenius element at an unramified `Q`
  generates the decomposition group of `Q`.
* `Ideal.card_stabilizer_eq_inertiaDeg_of_isUnramifiedAt`: the decomposition group of an
  unramified `Q` has order the inertia degree of `Q` over `𝓞 K`.
* `Ideal.stabilizerEquivResidueAut`: the decomposition group of an unramified prime is
  isomorphic to the automorphism group of the residue extension.
* `Ideal.isCyclic_stabilizer_of_isUnramifiedAt`: the decomposition group of an unramified
  prime is cyclic.
* `Ideal.zpowers_sup_inertia_eq_stabilizer_of_isArithFrobAt`: at any nonzero prime `Q`, a
  Frobenius element together with the inertia subgroup generates the decomposition group.
* `Ideal.orbit_stabilizer_eq_orbit_zpowers_of_isArithFrobAt`: on a set where the inertia
  subgroup acts trivially, the orbits of the decomposition group are those of any Frobenius.
* `Ideal.isArithFrobAt_pointwise_smul_iff_eq_conj`: the Frobenius elements at `τ • Q` are
  exactly the conjugates `τ σ τ⁻¹` of the Frobenius elements `σ` at an unramified `Q`.

## Implementation notes

`FiniteField.frobeniusAlgEquivOfAlgebraic` is stated for a `Fintype` base field, so the residue
identification supplies that instance internally through `Fintype.ofFinite`. Residue rings are
made into fields by the local instance `Ideal.Quotient.field`, following Mathlib's own
ramification files.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
-/

 section

open _root_.Ideal _root_.Module

open scoped _root_.NumberField _root_.Pointwise

namespace Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-! ### Unramifiedness and the inertia subgroup -/

/-- **Unramified means trivial inertia.** For a finite Galois extension `L / K` of number fields,
`L / K` is unramified at a prime `Q` of `𝓞 L` exactly when the inertia subgroup of `Q` in
`Gal(L/K)` is trivial.

This is the group-theoretic reading of `Ideal.card_inertia_eq_ramificationIdx`: the inertia
subgroup has as many elements as the ramification index of `Q` over `𝓞 K`. -/
theorem isUnramifiedAt_iff_inertia_eq_bot (Q : Ideal (𝓞 L)) [Q.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 K) Q ↔ Q.inertia (L ≃ₐ[K] L) = ⊥ := by
  rw [← Ideal.ramificationIdx_eq_one_iff (R := 𝓞 K) (q := Q),
    ← Ideal.card_inertia_eq_ramificationIdx (𝓞 K) (L ≃ₐ[K] L) Q]
  exact ⟨Subgroup.eq_bot_of_card_eq _, fun h ↦ by rw [h]; simp⟩

/-! ### The decomposition group at an unramified prime -/

/-- **The decomposition group of an unramified prime embeds in the residue Galois group.**
Mathlib's `Ideal.Quotient.stabilizerHom` has the inertia subgroup as its kernel, and that
subgroup is trivial at an unramified prime. -/
theorem stabilizerHom_injective_of_isUnramifiedAt (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] :
    Function.Injective (Ideal.Quotient.stabilizerHom Q (Q.under (𝓞 K)) (L ≃ₐ[K] L)) := by
  rw [← MonoidHom.ker_eq_bot_iff, Ideal.Quotient.ker_stabilizerHom, eq_bot_iff]
  intro σ hσ
  have hσ' : (σ : L ≃ₐ[K] L) ∈ Q.inertia (L ≃ₐ[K] L) := Ideal.coe_mem_inertia.mpr hσ
  rw [(isUnramifiedAt_iff_inertia_eq_bot Q).mp ‹_›, Subgroup.mem_bot] at hσ'
  exact Subgroup.mem_bot.mpr (Subtype.ext hσ')







attribute [local instance] Ideal.Quotient.field

omit [IsGalois K L] in
/-- **A Frobenius element induces the residue Frobenius.** The action of an arithmetic Frobenius
`σ` at `Q` on the residue field `𝓞 L ⧸ Q` is the `#(𝓞 K ⧸ 𝔭)`-power map, that is
`FiniteField.frobeniusAlgEquivOfAlgebraic` of the residue extension.

This is the defining congruence `σ x ≡ x ^ #(𝓞 K ⧸ 𝔭) (mod Q)` read as an equality of
automorphisms of `𝓞 L ⧸ Q`; no unramifiedness is needed. -/
theorem stabilizerHom_eq_frobeniusAlgEquivOfAlgebraic (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    let _ : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ
    letI := Fintype.ofFinite (𝓞 K ⧸ Q.under (𝓞 K))
    Ideal.Quotient.stabilizerHom Q (Q.under (𝓞 K)) (L ≃ₐ[K] L) ⟨σ, hσ.mem_stabilizer⟩ =
      FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 K ⧸ Q.under (𝓞 K)) (𝓞 L ⧸ Q) := by
  let _ : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.stabilizerHom_apply, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    ← @Nat.card_eq_fintype_card _ (Fintype.ofFinite _)]
  simpa [MulAction.subgroup_smul_def, MulSemiringAction.toAlgHom_apply] using hσ.mk_apply x

/-- **The order of a Frobenius element is the inertia degree.** For `Q` unramified over `𝓞 K`, an
arithmetic Frobenius `σ` at `Q` has `orderOf σ = f(Q / 𝔭)`.

The decomposition group injects into the residue Galois group, where the image of `σ` is the
residue Frobenius; that automorphism has order the degree of the residue extension, which is the
inertia degree. -/
theorem orderOf_eq_inertiaDeg_of_isArithFrobAt (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) [Algebra.IsUnramifiedAt (𝓞 K) Q] {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    orderOf σ = Q.inertiaDeg (𝓞 K) := by
  let _ : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ
  have : Fintype (𝓞 K ⧸ Q.under (𝓞 K)) := Fintype.ofFinite _
  have key : orderOf (⟨σ, hσ.mem_stabilizer⟩ : MulAction.stabilizer (L ≃ₐ[K] L) Q) =
      Q.inertiaDeg (𝓞 K) := by
    rw [← orderOf_injective _ (stabilizerHom_injective_of_isUnramifiedAt Q),
      stabilizerHom_eq_frobeniusAlgEquivOfAlgebraic Q hQ hσ,
      FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
      Ideal.inertiaDeg_eq_of_isMaximal (Q.under (𝓞 K)) Q]
  exact (Subgroup.orderOf_coe (⟨σ, hσ.mem_stabilizer⟩ :
    MulAction.stabilizer (L ≃ₐ[K] L) Q)).trans key







/-! ### The decomposition group at a possibly ramified prime -/







/-! ### Conjugation along the fibre -/



end Ideal

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
# The residue degree of a height-one prime over `ℚ`

A height-one prime `𝔭` of `𝓞 K` lies over a unique rational prime `p`, and its absolute norm is
`p ^ f` for `f` the residue degree `Ideal.inertiaDeg 𝔭.asIdeal ℤ`.  This file names the two
objects that description involves and records their elementary theory.

## Main definitions

* `TauCeti.rationalPrimeBelow 𝔭` is the rational prime below a height-one prime `𝔭` of `𝓞 K`,
  namely the absolute norm of `𝔭 ∩ ℤ`.
* `TauCeti.higherDegreePrimes K` is the set of height-one primes of `𝓞 K` whose residue degree
  over `ℚ` exceeds `1`.
* `TauCeti.primesDividing K n hn` is the finite set of height-one primes of `𝓞 K` whose rational
  prime below divides a nonzero integer `n`.

## Main results

* `TauCeti.absNorm_eq_rationalPrimeBelow_pow`: the absolute norm of `𝔭` is the rational prime
  below it raised to the residue degree.
* `TauCeti.mem_higherDegreePrimes_iff_not_prime_absNorm`: a height-one prime has residue degree
  above one exactly when its absolute norm is not a prime number.
* `TauCeti.rationalPrimeBelow_pow_le_absNorm`: the norm of `𝔭` is at least the rational prime
  below it raised to any power at most the residue degree.
* `TauCeti.mem_higherDegreePrimes_of_one_lt_inertiaDeg`: residue degree above one over an
  intermediate number field forces residue degree above one over `ℚ`.
* `TauCeti.card_filter_rationalPrimeBelow_le_finrank`: at most `[K : ℚ]` height-one primes have
  a given rational prime below them.
* `IsDedekindDomain.HeightOneSpectrum.encard_setOf_under_eq_le_finrank`: at most `[E : K]`
  height-one primes of `E` contract to a given height-one prime of an intermediate number field
  `K`.
* `IsDedekindDomain.HeightOneSpectrum.absNorm_dvd_rationalPrimeBelow_pow_finrank`: the absolute
  norm of `𝔭` divides `p ^ [K : ℚ]`, so the residue degree is at most the degree of the field.
* `TauCeti.asIdeal_eq_span_singleton_of_absNorm_eq_pow_finrank`: a prime of full residue degree
  is inert, that is, generated by the rational prime below it.
* `IsDedekindDomain.HeightOneSpectrum.intCast_mem_asIdeal_iff`: an integer belongs to a
  height-one prime exactly when the rational prime below it divides that integer.
* `TauCeti.mem_primesDividing`: the defining condition for membership in `primesDividing`.

## Implementation notes

`rationalPrimeBelow` is named rather than spelled out as `Ideal.absNorm (Ideal.under ℤ 𝔭.asIdeal)`
because the estimates downstream fibre the primes over it: keeping it a single head symbol is what
makes the fibrewise rewriting elaborate, and it is the object `Chebotarev` will name when it
compares a prime of `K` with the rational prime under it.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §8.
-/

 section

open _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]





/-! ### The rational prime below a height-one prime -/







omit [NumberField K] in
/-- The rational prime below a height-one prime really is a prime number. -/
theorem prime_rationalPrimeBelow (𝔭 : HeightOneSpectrum (𝓞 K)) :
    (rationalPrimeBelow 𝔭).Prime := by
  have : NeZero 𝔭.asIdeal := ⟨𝔭.ne_bot⟩
  exact Nat.absNorm_under_prime 𝔭.asIdeal

/-- The absolute norm of a height-one prime is the rational prime below it raised to the residue
degree. -/
theorem absNorm_eq_rationalPrimeBelow_pow (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm 𝔭.asIdeal =
      rationalPrimeBelow 𝔭 ^ Ideal.inertiaDeg 𝔭.asIdeal ℤ :=
  (Ideal.absNorm_pow_inertiaDeg (Ideal.under ℤ 𝔭.asIdeal) 𝔭.asIdeal).symm



/-- The absolute norm of a height-one prime is at least the rational prime below it raised to any
exponent bounded by the residue degree.  The matching bound from above is the divisibility
`IsDedekindDomain.HeightOneSpectrum.absNorm_dvd_rationalPrimeBelow_pow_finrank`.  Use
`TauCeti.absNorm_eq_rationalPrimeBelow_pow` for the exact value instead, and
`TauCeti.mem_higherDegreePrimes` to supply the hypothesis at the common instance `n = 2`. -/
theorem rationalPrimeBelow_pow_le_absNorm {𝔭 : HeightOneSpectrum (𝓞 K)} {n : ℕ}
    (hn : n ≤ Ideal.inertiaDeg 𝔭.asIdeal ℤ) : rationalPrimeBelow 𝔭 ^ n ≤ Ideal.absNorm 𝔭.asIdeal :=
  -- the norm is `p ^ f`, and `p` is at least `2`, so the power is monotone in the exponent
  absNorm_eq_rationalPrimeBelow_pow 𝔭 ▸
    Nat.pow_le_pow_right (prime_rationalPrimeBelow 𝔭).one_lt.le hn



/-! ### Fibring the primes over the rational primes below them -/





/-! ### Inert primes -/







/-! ### The primes dividing an integer -/









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
# The primes of residue degree above one are negligible

A height-one prime `𝔭` of `𝓞 K` lies over a unique rational prime `p`, and its absolute norm is
`p ^ f` for `f` the residue degree `Ideal.inertiaDeg 𝔭.asIdeal ℤ`.  This file bounds the
contribution of the primes with `f ≥ 2`, the set `TauCeti.higherDegreePrimes K`: they number
`O(√x)` up to norm `x`, hence also `o(x / log x)`, and their Dirichlet series `∑ N(𝔭) ^ (-s)`
converges for every `s > 1/2`, with a bound that is uniform on `s ≥ 1`.

Two elementary inputs carry the whole argument.

* A prime with `f ≥ 2` has `N(𝔭) = p ^ f ≥ p ^ 2`, so it is *not* determined by a rational prime
  of size `N(𝔭)` but by one of size at most `√(N(𝔭))`.
* At most `[K : ℚ]` height-one primes lie over one rational prime, by the fundamental identity
  `∑ e f = [K : ℚ]`; this is the already available
  `TauCeti.card_filter_rationalPrimeBelow_le_finrank`, itself resting on
  `TauCeti.NumberField.card_primesOverFinset_le_finrank`.

Together these compare any finite sum over the degree-above-one primes with `[K : ℚ]` times a sum
over the rational primes with the exponent doubled, which is
`TauCeti.sum_absNorm_rpow_higherDegreePrimes_le_finrank_mul_tsum` below.  Counting gives the
`O(√x)` bound, and summing `m ^ (-2s)` gives convergence for every `s > 1/2` together with a
bound on the partial Dirichlet series that is *uniform* on `s ≥ 1`.

## Main results

* `TauCeti.primeCount_higherDegreePrimes_le`: the explicit count
  `π_K(x; f ≥ 2) ≤ [K : ℚ] · √x`, with `TauCeti.primeCount_higherDegreePrimes_isBigO` and
  `TauCeti.primeCount_higherDegreePrimes_isLittleO` its `O(√x)` and `o(x / log x)` forms.
* `TauCeti.summable_absNorm_rpow_higherDegreePrimes`: `∑ N(𝔭) ^ (-s)` over the degree-above-one
  primes converges for every `s > 1/2`, in particular at `s = 1`.
* `TauCeti.primeTheta_higherDegreePrimes_isLittleO`: those primes carry weight `o(x)` in `ϑ_K`.
* `TauCeti.primeIdealZetaSum_higherDegreePrimes_le`: that sum, in Mathlib's
  `NumberField.Set.primeIdealZetaSum` vocabulary, is at most `2 [K : ℚ]` for every `s ≥ 1`.
* `TauCeti.sum_absNorm_rpow_le_finrank_mul_tsum` and
  `TauCeti.tsum_absNorm_rpow_le_finrank_mul_tsum`: the same fibring over *all* height-one primes,
  in finite and infinite form, for every `s > 1`.
* `TauCeti.tsum_absNorm_rpow_neg_two_le`: at `s = 2` that becomes the explicit
  `∑_𝔭 N(𝔭) ^ (-2) ≤ 2 [K : ℚ]`.

No density-zero statement is proved here.  What this file supplies is the numerator half of
one: `NumberField.Set.HasDirichletDensity (higherDegreePrimes K) 0` asks for
`primeIdealZetaSum (higherDegreePrimes K) s / primeIdealZetaSum univ s → 0` as `s → 1⁺`, and the
bound below controls only the numerator.  Together with the divergence of the denominator it gives
`TauCeti.hasDirichletDensity_higherDegreePrimes` in
`TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Negligible`.  By contrast
`primeCount K (higherDegreePrimes K) =o[atTop] primeCount K univ`
would need a lower bound on the full prime count, which the prime ideal theorem supplies and
which is not available here; the `o(x / log x)` statement below is against the explicit
function `x / log x`, not against `π_K`.

## Implementation notes

The set `TauCeti.higherDegreePrimes` and the map `TauCeti.rationalPrimeBelow` the estimates fibre
over, together with their elementary norm and inertia theory, are algebraic rather than analytic
and live in `TauCeti.NumberTheory.NumberField.ResidueDegree`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, and J. Milne, *Algebraic Number Theory*,
  Chapter VIII, for the same estimate in the Dirichlet-density setting.
-/

 section

open _root_.Asymptotics _root_.Filter _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-! ### Fibring a sum over the rational primes below the primes -/

/-- Comparison of a finite sum over height-one primes with a sum over the rational primes below
them: the fibres have at most `[K : ℚ]` elements. -/
theorem sum_comp_rationalPrimeBelow_le {g : ℕ → ℝ} {F : Finset (HeightOneSpectrum (𝓞 K))}
    {T : Finset ℕ} (hg : ∀ m ∈ T, 0 ≤ g m) (hFT : ∀ 𝔭 ∈ F, rationalPrimeBelow 𝔭 ∈ T) :
    ∑ 𝔭 ∈ F, g (rationalPrimeBelow 𝔭) ≤ Module.finrank ℚ K * ∑ m ∈ T, g m := by
  rw [← Finset.sum_fiberwise_of_maps_to' hFT g, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm ↦ ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right
    (mod_cast card_filter_rationalPrimeBelow_le_finrank F m) (hg m hm)

/-- Comparison of a finite sum over height-one primes with the *whole* sum over `ℕ`: fibring
costs a factor `[K : ℚ]`, and completing the finite rational-prime sum to its `tsum` costs
nothing because the summand is nonnegative. This is the shape both norm-sum bounds below
take, once each has compared its own summand termwise with `g (rationalPrimeBelow 𝔭)`. -/
theorem sum_comp_rationalPrimeBelow_le_finrank_mul_tsum {g : ℕ → ℝ} (hg : ∀ m, 0 ≤ g m)
    (hsum : Summable g) (F : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑ 𝔭 ∈ F, g (rationalPrimeBelow 𝔭) ≤ Module.finrank ℚ K * ∑' m : ℕ, g m :=
  (sum_comp_rationalPrimeBelow_le (fun m _ ↦ hg m)
        fun _ ↦ Finset.mem_image_of_mem rationalPrimeBelow).trans
    (mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun m _ ↦ hg m) (Nat.cast_nonneg _))

/-! ### Counting the primes of residue degree above one -/











/-! ### Convergence of the prime Dirichlet series over the degree-above-one primes -/








/-! ### All height-one primes -/

/-- **A finite norm sum is at most `[K : ℚ]` times the sum of `m ^ (-s)` over `ℕ`.** Fibring a
finite sum of `N(𝔭) ^ (-s)` over the rational primes below costs a factor `[K : ℚ]`. Without a
residue-degree hypothesis only `p ≤ N(𝔭)` is available, so the exponent stays `-s` and the
argument needs `1 < s`; the degree-above-one analogue
`TauCeti.sum_absNorm_rpow_higherDegreePrimes_le_finrank_mul_tsum` gains the exponent `-2s` and so
reaches down to `s > 1/2`. -/
theorem sum_absNorm_rpow_le_finrank_mul_tsum {s : ℝ} (hs : 1 < s)
    (F : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑ 𝔭 ∈ F, (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ Module.finrank ℚ K * ∑' m : ℕ, (m : ℝ) ^ (-s) :=
  (Finset.sum_le_sum fun 𝔭 _ ↦ by
        have hpN : rationalPrimeBelow 𝔭 ≤ Ideal.absNorm 𝔭.asIdeal := by
          simpa using rationalPrimeBelow_pow_le_absNorm (𝔭.asIdeal.inertiaDeg_pos ℤ)
        exact Real.rpow_le_rpow_of_nonpos (mod_cast (prime_rationalPrimeBelow 𝔭).pos)
          (mod_cast hpN) (by linarith)).trans
    (sum_comp_rationalPrimeBelow_le_finrank_mul_tsum
      (fun m ↦ Real.rpow_nonneg (Nat.cast_nonneg m) _)
      (Real.summable_nat_rpow.mpr (by linarith)) F)

/-- **The prime ideal zeta sum is at most `[K : ℚ]` times the sum of `m ^ (-s)` over `ℕ`.** The
finite-sum comparison passes to the limit on the whole range `1 < s` where both sides converge.
Specializing the exponent is what buys an explicit constant, as in
`TauCeti.tsum_absNorm_rpow_neg_two_le`. -/
theorem tsum_absNorm_rpow_le_finrank_mul_tsum {s : ℝ} (hs : 1 < s) :
    ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤
      Module.finrank ℚ K * ∑' m : ℕ, (m : ℝ) ^ (-s) :=
  Real.tsum_le_of_sum_le (fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (sum_absNorm_rpow_le_finrank_mul_tsum hs)

/-- **The prime ideal zeta sum over all height-one primes at `s = 2` is at most `2 [K : ℚ]`.**
At most `[K : ℚ]` primes lie over each rational prime, and `ζ (2) < 2`.  The same constant bounds
the degree-above-one primes for every `s ≥ 1`: `TauCeti.primeIdealZetaSum_higherDegreePrimes_le`.
The constant is available only from `s = 2` upwards: at `s` just above `1` the sum over `ℕ` is
already larger than `2`, so only the `s`-dependent bound above survives there. -/
theorem tsum_absNorm_rpow_neg_two_le :
    ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(2 : ℝ)) ≤
      2 * Module.finrank ℚ K :=
  ((tsum_absNorm_rpow_le_finrank_mul_tsum one_lt_two).trans <| mul_le_mul_of_nonneg_left
    (tsum_nat_rpow_neg_le_two le_rfl) (Nat.cast_nonneg _)).trans_eq (mul_comm _ _)

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
# The real Euler product of the Dedekind zeta function in exponential form

For real `s > 1`, every local ratio `x = N(𝔭) ^ (-s)` of a height-one prime lies in `(0, 1/2]`,
because `N(𝔭) ≥ 2`. The principal logarithm of each Euler factor is then the real number
`-log (1 - x)`, and the exponential form
`TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries` of the Euler product,
specialized to the trivial weight, becomes a statement about real numbers: `ζ_K(s)` is the
exponential of the convergent real sum `∑_𝔭 -log (1 - N(𝔭) ^ (-s))`. In particular `ζ_K(s)` is a
positive real number, and that sum is its real logarithm.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.absNorm_rpow_neg_le_half`: `N(𝔭) ^ (-s) ≤ 1/2`
  for `1 ≤ s`.
* `TauCeti.summable_neg_log_one_sub_absNorm_rpow`: `∑_𝔭 -log (1 - N(𝔭) ^ (-s))` converges for
  `1 < s`.
* `TauCeti.dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub`: for real `s > 1`, `ζ_K(s)` is the
  exponential of that real sum.
* `TauCeti.dedekindZeta_re_eq_exp` and `TauCeti.dedekindZeta_re_pos`: the same for the real part,
  which is therefore positive.
* `TauCeti.log_dedekindZeta_re_eq_tsum_neg_log_one_sub`: that real sum is the real logarithm of
  `ζ_K(s)`.

## References

* The real logarithmic identity also appears, under the same name, in the
  Birkbeck–Brasca Chebotarev density project, <https://github.com/CBirkbeck/chebotarev-density>
  (Apache-2.0), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, file
  `CebotarevDensity/Density.lean`, where it is proved from `Real.hasProd_of_hasSum_log` and the
  product formula. It is derived here instead from TauCeti's exponential Euler product
  `TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries`.
-/

 section

open _root_.IsDedekindDomain _root_.NumberField

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

/-- For `1 ≤ s`, the local ratio `N(𝔭) ^ (-s)` of a height-one prime is at most `1/2`, because
`N(𝔭) ≥ 2`. -/
theorem absNorm_rpow_neg_le_half (P : HeightOneSpectrum (𝓞 K)) {s : ℝ} (hs : 1 ≤ s) :
    (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) ≤ 1 / 2 :=
  Real.rpow_neg_le_half (TauCeti.two_le_absNorm_asIdeal_real P) hs

end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- For `1 < s`, the real logarithms `-log (1 - N(𝔭) ^ (-s))` of the Euler factors of the Dedekind
zeta function are summable over the height-one primes. -/
theorem summable_neg_log_one_sub_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦
      -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) := by
  refine ((summable_absNorm_rpow_primes_of_one_lt hs).mul_left 2).of_nonneg_of_le
    (fun P ↦ (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans (by
      have hpos : 0 < 1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) := by
        linarith [P.absNorm_rpow_neg_le_half hs.le]
      linarith [Real.log_le_sub_one_of_pos hpos])) (fun P ↦ ?_)
  -- On `[0, 1/2]`, `x + 2 x ^ 2 ≤ 2 x`.
  have hx0 : 0 ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) := by positivity
  have hx := P.absNorm_rpow_neg_le_half hs.le
  nlinarith [Real.neg_log_one_sub_le_add_two_mul_sq hx0 hx]



/-- For real `s > 1`, the real part of `ζ_K(s)` is the exponential of `∑_𝔭 -log (1 - N(𝔭) ^ (-s))`.
-/
theorem dedekindZeta_re_eq_exp {s : ℝ} (hs : 1 < s) :
    (dedekindZeta K s).re = Real.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s))) := by
  rw [dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub hs, Complex.ofReal_re]

/-- **The real logarithm of the Dedekind zeta function.** For real `s > 1`, the real logarithm of
`ζ_K(s)` is the convergent sum `∑_𝔭 -log (1 - N(𝔭) ^ (-s))` over the height-one primes of `𝓞 K`.
-/
theorem log_dedekindZeta_re_eq_tsum_neg_log_one_sub {s : ℝ} (hs : 1 < s) :
    Real.log (dedekindZeta K s).re = ∑' P : HeightOneSpectrum (𝓞 K),
      -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) := by
  rw [dedekindZeta_re_eq_exp hs, Real.log_exp]



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
# The higher prime powers in the logarithm of the Dedekind Euler product

Taking logarithms in the Euler product `ζ_K(s) = ∏_𝔭 (1 - N(𝔭) ^ (-s))⁻¹` turns it into the
double sum `∑_𝔭 ∑_{m ≥ 1} N(𝔭) ^ (-m s) / m`, whose `m = 1` part is the prime Dirichlet series
`NumberField.Set.primeIdealZetaSum Set.univ s`.  This file bounds everything else: the `m ≥ 2`
part, equivalently the difference `∑_𝔭 (-log (1 - N(𝔭) ^ (-s)) - N(𝔭) ^ (-s))`, is nonnegative
and at most `2 [K : ℚ]`.

The bound is uniform on all of `s ≥ 1`, endpoint included, and that endpoint is the whole point:
at `s = 1` the Euler-factor logarithm sum and the prime Dirichlet series each diverge, while
their termwise difference still converges, because discarding the linear term of
`-log (1 - x)` replaces the exponent `-s` by the exponent `-2 s`, and `2 s ≥ 2` already
converges.

Two elementary inputs carry the argument.

* A height-one prime `𝔭` has `N(𝔭) ≥ 2`, so `N(𝔭) ^ (-s) ≤ 1 / 2` for `s ≥ 1` and the
  denominator `1 - N(𝔭) ^ (-s)` is bounded below by `1 / 2`; the termwise difference is
  therefore at most `N(𝔭) ^ (-2)`.
* `N(𝔭)` is at least the rational prime below `𝔭` and at most `[K : ℚ]` primes lie over one
  rational prime, so `∑_𝔭 N(𝔭) ^ (-2) ≤ 2 [K : ℚ]`.  That bound is not proved again here: it is
  the imported `TauCeti.tsum_absNorm_rpow_neg_two_le`.

## Main results

* `TauCeti.summable_neg_log_one_sub_sub_absNorm_rpow`: the termwise difference between the
  Euler-factor logarithm and the prime Dirichlet term is summable for every `s > 1 / 2`.
* `TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_nonneg`: termwise nonnegativity for `s > 0`
  yields a nonnegative `tsum`; convergence is supplied separately for `s > 1 / 2`.
* `TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_le`: it is at most `2 [K : ℚ]` for every
  `s ≥ 1`; together the two bound the sum in `[0, 2 [K : ℚ]]` on `s ≥ 1`.
* `TauCeti.abs_tsum_neg_log_one_sub_sub_primeIdealZetaSum_le`: for `s > 1`, where the
  two sums converge separately, the sum of the Euler-factor logarithms differs from
  `NumberField.Set.primeIdealZetaSum Set.univ s` by at most `2 [K : ℚ]`.

## Implementation notes

The constant is explicit rather than existentially quantified, and the upper bound's hypothesis
is the closed condition `1 ≤ s` rather than a neighbourhood of `1`: both are free here, and a
consumer that wants an eventual statement near `s = 1` gets it by weakening, whereas the
converse costs work.

The two halves carry different hypotheses on purpose. Nonnegativity holds as soon as
`N(𝔭) ^ (-s) < 1`, so it is stated on `0 < s`; the uniform upper bound uses
`N(𝔭) ^ (-s) ≤ 1 / 2`. No uniform bound can persist as `s ↓ 1 / 2`, where the dominating
prime series approaches its convergence endpoint.

The one-variable estimate behind the termwise bound is not proved again: it is Mathlib's
`Complex.norm_log_one_sub_inv_sub_self_le` read along the reals, which is where the factor `2`
in the denominator below comes from.

Convergence of `∑_𝔭 N(𝔭) ^ (-s)` over all height-one primes for `1 < s` is not proved again
either: it is `TauCeti.summable_absNorm_rpow_primes_of_one_lt`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §3.
* C. Birkbeck and R. Brasca, `CebotarevDensity/Density.lean` in
  [CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density), Apache-2.0,
  commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, declarations
  `primeIdealZetaHigherTail_bounded` and `neg_log_one_sub_sub_le`.
-/

 section

open _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-! ### The prime-power tail -/

/-- **The prime-power tail is summable.** The termwise difference between the Euler-factor
logarithm `-log (1 - N(𝔭) ^ (-s))` and the prime Dirichlet term `N(𝔭) ^ (-s)` is summable for
every `s > 1 / 2`; at `s = 1` this remains summable although either of the two families from which
it is built is not. -/
theorem summable_neg_log_one_sub_sub_absNorm_rpow {s : ℝ} (hs : 1 / 2 < s) :
    Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
  have hs0 : 0 < s := by linarith
  have hs2 : 1 < 2 * s := by linarith
  have hsum := (summable_absNorm_rpow_primes_of_one_lt (K := K) hs2).mul_left
    ((2 * (1 - (2 : ℝ) ^ (-s)))⁻¹)
  refine hsum.of_nonneg_of_le
    (fun 𝔭 ↦ Real.neg_log_one_sub_rpow_sub_nonneg
      (one_lt_two.trans_le (two_le_absNorm_asIdeal_real 𝔭)) hs0) ?_
  intro 𝔭
  simpa only [div_eq_mul_inv, mul_comm] using
    Real.neg_log_one_sub_rpow_sub_le_div (two_le_absNorm_asIdeal_real 𝔭) hs0

/-- **The prime-power tail is termwise nonnegative.** For every `s > 0`, termwise nonnegativity
yields a nonnegative `tsum`. This statement does not assert summability; that is supplied by
`TauCeti.summable_neg_log_one_sub_sub_absNorm_rpow` for `s > 1 / 2`. -/
theorem tsum_neg_log_one_sub_sub_absNorm_rpow_nonneg {s : ℝ} (hs : 0 < s) :
    0 ≤ ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (-Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) :=
  tsum_nonneg fun 𝔭 ↦ Real.neg_log_one_sub_rpow_sub_nonneg
    (one_lt_two.trans_le (two_le_absNorm_asIdeal_real 𝔭)) hs

/-- **The prime-power tail is bounded uniformly on `s ≥ 1`.** The constant `2 [K : ℚ]` does not
depend on `s`, so this survives the passage to the limit `s → 1⁺` that the Dirichlet-density
normalization needs. -/
theorem tsum_neg_log_one_sub_sub_absNorm_rpow_le {s : ℝ} (hs : 1 ≤ s) :
    ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (-Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) ≤ 2 * Module.finrank ℚ K :=
  ((summable_neg_log_one_sub_sub_absNorm_rpow (K := K)
      ((by norm_num : (1 / 2 : ℝ) < 1).trans_le hs)).tsum_le_tsum
    (fun 𝔭 ↦ Real.neg_log_one_sub_rpow_sub_le (two_le_absNorm_asIdeal_real 𝔭) hs)
    (summable_absNorm_rpow_primes_of_one_lt one_lt_two)).trans tsum_absNorm_rpow_neg_two_le

/-- **The Euler-factor logarithms sum to the prime Dirichlet series up to `O(1)`.** For `s > 1`,
where both series converge, `∑_𝔭 -log (1 - N(𝔭) ^ (-s))` differs from
`NumberField.Set.primeIdealZetaSum Set.univ s` by at most the constant `2 [K : ℚ]`.

The absolute value is here so that the statement can be used directly as an `O(1)` estimate; the
difference is in fact nonnegative — see `TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_nonneg`. -/
theorem abs_tsum_neg_log_one_sub_sub_primeIdealZetaSum_le {s : ℝ} (hs : 1 < s) :
    |(∑' 𝔭 : HeightOneSpectrum (𝓞 K), -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))) -
      NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s| ≤ 2 * Module.finrank ℚ K := by
  have hsumP := TauCeti.summable_absNorm_rpow_primes_of_one_lt (K := K) hs
  have hsumL : Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := by
    simpa using (TauCeti.summable_neg_log_one_sub_sub_absNorm_rpow (K := K)
      ((by norm_num : (1 / 2 : ℝ) < 1).trans hs)).add hsumP
  -- Both series converge separately, so their difference is the sum of the prime-power tail.
  rw [NumberField.Set.primeIdealZetaSum_def, tsum_univ fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s), ← hsumL.tsum_sub hsumP,
    abs_of_nonneg (TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_nonneg (zero_lt_one.trans hs))]
  exact TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_le hs.le

end TauCeti

end
end

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The all-prime Dirichlet sum is `log (1 / (s - 1)) + O(1)`

For a number field `K`, write `P(s) = ∑_𝔭 N(𝔭) ^ (-s)` for the sum over all height-one primes of
`𝓞 K`, which is `NumberField.Set.primeIdealZetaSum Set.univ s`. This file proves that
`P(s) = log (1 / (s - 1)) + O(1)` as `s → 1⁺`, and hence that Mathlib's ratio-normalized
`NumberField.Set.HasDirichletDensity` agrees with the logarithmically normalized density.

The proof has two inputs, and neither suffices alone.

* **The Euler product.** For real `s > 1`, `log ζ_K(s)` is the convergent sum
  `∑_𝔭 -log (1 - N(𝔭) ^ (-s))`, by `TauCeti.log_dedekindZeta_re_eq_tsum_neg_log_one_sub`.
  The higher-prime-power tail theorem
  `TauCeti.abs_tsum_neg_log_one_sub_sub_primeIdealZetaSum_le` bounds the difference from `P(s)`
  by `2 [K : ℚ]`, uniformly for `s > 1`.
* **The residue.** Mathlib's class number formula
  `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` says that `(s - 1) ζ_K(s)` tends to the
  positive residue as `s → 1⁺`, so `log ζ_K(s) - log (1 / (s - 1))` tends to its logarithm.

## Main results

* `TauCeti.primeIdealZetaSum_univ_le_log_dedekindZeta_re` and
  `TauCeti.log_dedekindZeta_re_le_primeIdealZetaSum_univ_add`: the two-sided comparison of
  `log ζ_K(s)` with `P(s)`, with error at most `2 [K : ℚ]`.
* `TauCeti.tendsto_log_dedekindZeta_re_sub_log_one_div_sub_one`: `log ζ_K(s) - log (1 / (s - 1))`
  tends to the logarithm of the residue.
* `TauCeti.primeIdealZetaSum_univ_sub_log_one_div_sub_one_isBigO`:
  `P(s) - log (1 / (s - 1)) = O(1)` as `s → 1⁺`.
* `TauCeti.tendsto_primeIdealZetaSum_univ_atTop`: `P(s) → ∞` as `s → 1⁺`.
* `TauCeti.tendsto_primeIdealZetaSum_univ_div_log_one_div_sub_one`:
  `P(s) / log (1 / (s - 1)) → 1` as `s → 1⁺`.
* `NumberField.Set.hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one`: a set of primes has
  Dirichlet density `δ` exactly when `P_S(s) / log (1 / (s - 1)) → δ`.
* `NumberField.Set.ofReal_primeIdealZetaSum`: `P_S(t)`, cast to `ℂ`, is the complex sum over all
  primes of the indicator of `S` against `N(𝔭) ^ (-t)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.1.
* The same argument (Sharifi, *Algebraic Number Theory*, 7.1.12) is formalized in the
  Birkbeck–Brasca Chebotarev density project, <https://github.com/CBirkbeck/chebotarev-density>
  (Apache-2.0), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, file
  `CebotarevDensity/Density.lean`: `primeIdealZetaSum_univ_tendsto_log` and
  `primeIdealZetaSum_univ_tendsto_atTop`, closed there by the helpers of
  `CebotarevDensity/ForMathlib/LogOneDivSubOne.lean` that `Real.tendsto_log_one_div_sub_atTop`
  and `TauCeti.tendsto_div_nhds_one_of_le_add_const_of_sub_const_le` adapt. This file follows
  its outline (Euler-product logarithm, bounded higher-prime-power contribution, simple pole),
  over `HeightOneSpectrum` rather than the nonzero prime ideals of `𝓞 K`. It derives the
  logarithmic form of the Euler product from
  `TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries` and uses the explicit
  higher-prime-power bound from
  `TauCeti.abs_tsum_neg_log_one_sub_sub_primeIdealZetaSum_le`.
-/

 section

open _root_.Filter _root_.Asymptotics _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.Topology

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- **The prime sum is at most `log ζ_K(s)`.** For real `s > 1`, the sum of `N(𝔭) ^ (-s)` over all
height-one primes is at most the real logarithm of `ζ_K(s)`. -/
theorem primeIdealZetaSum_univ_le_log_dedekindZeta_re {s : ℝ} (hs : 1 < s) :
    (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s ≤
      Real.log (dedekindZeta K s).re := by
  rw [log_dedekindZeta_re_eq_tsum_neg_log_one_sub hs, Set.primeIdealZetaSum_univ]
  exact (summable_absNorm_rpow_primes_of_one_lt hs).tsum_le_tsum
    (fun P ↦ by
      have hpos : 0 < 1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) := by
        linarith [P.absNorm_rpow_neg_le_half hs.le]
      linarith [Real.log_le_sub_one_of_pos hpos])
    (summable_neg_log_one_sub_absNorm_rpow hs)

/-- **`log ζ_K(s)` exceeds the prime sum by at most `2 [K : ℚ]`.** For real `s > 1`, the real
logarithm of `ζ_K(s)` is at most the all-prime sum at `s` plus `2 [K : ℚ]`, a constant independent
of `s` that bounds the contribution of the higher prime powers. -/
theorem log_dedekindZeta_re_le_primeIdealZetaSum_univ_add {s : ℝ} (hs : 1 < s) :
    Real.log (dedekindZeta K s).re ≤
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s +
        2 * Module.finrank ℚ K := by
  rw [log_dedekindZeta_re_eq_tsum_neg_log_one_sub hs]
  have h := (abs_le.mp
    (abs_tsum_neg_log_one_sub_sub_primeIdealZetaSum_le (K := K) hs)).2
  linarith

/-! ### The residue and the logarithmic normalization -/



/-- The all-prime sum stays within a bounded distance of `log (1 / (s - 1))` near `1⁺`. -/
private theorem exists_abs_primeIdealZetaSum_univ_sub_log_one_div_sub_one_le :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      |(Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s -
        Real.log (1 / (s - 1))| ≤ C := by
  refine ⟨|Real.log (dedekindZeta_residue K)| + 1 +
    2 * Module.finrank ℚ K, ?_⟩
  have hnear : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      |Real.log (dedekindZeta K s).re - Real.log (1 / (s - 1))| ≤
        |Real.log (dedekindZeta_residue K)| + 1 := by
    refine (tendsto_log_dedekindZeta_re_sub_log_one_div_sub_one (K := K)).abs.eventually
      (ge_mem_nhds ?_)
    linarith
  filter_upwards [hnear, self_mem_nhdsWithin] with s hnear hs
  have h1 := primeIdealZetaSum_univ_le_log_dedekindZeta_re (K := K) hs
  have h2 := log_dedekindZeta_re_le_primeIdealZetaSum_univ_add (K := K) hs
  have h3 : (0 : ℝ) ≤ 2 * Module.finrank ℚ K := by positivity
  rw [abs_le] at hnear ⊢
  constructor <;> linarith [hnear.1, hnear.2]



/-- **The all-prime sum diverges at `1`.** The sum of `N(𝔭) ^ (-s)` over all height-one primes of
`𝓞 K` tends to `+∞` as `s → 1⁺`. -/
theorem tendsto_primeIdealZetaSum_univ_atTop :
    Tendsto (fun s : ℝ ↦ (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s)
      (𝓝[>] 1) atTop := by
  obtain ⟨C, hC⟩ := exists_abs_primeIdealZetaSum_univ_sub_log_one_div_sub_one_le (K := K)
  refine tendsto_atTop_mono' _ (hC.mono fun s hs ↦ ?_)
    (tendsto_atTop_add_const_right _ (-C) (Real.tendsto_log_one_div_sub_atTop 1))
  linarith [(abs_le.mp hs).1]



end TauCeti

namespace NumberField.Set

open _root_.TauCeti

variable {K : Type*} [Field K] [NumberField K]





end NumberField.Set

end
end

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
namespace TauCeti.NumberField
end TauCeti.NumberField
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Sets of primes of Dirichlet density zero

For a number field `K`, Mathlib's `NumberField.Set.HasDirichletDensity S δ` says that
`P_S(s) / P(s) → δ` as `s → 1⁺`, where `P_S(s) = ∑_{𝔭 ∈ S} N(𝔭) ^ (-s)` and `P` is the sum over
all height-one primes. Since `P(s) → ∞` as `s → 1⁺`
(`TauCeti.tendsto_primeIdealZetaSum_univ_atTop`), any set whose partial sum stays bounded near
`1` has Dirichlet density zero. This covers every finite set of primes, and every set whose
series `∑_{𝔭 ∈ S} N(𝔭)⁻¹` converges, such as the primes of residue degree greater than one.

A set of density zero is negligible: two sets whose symmetric difference has density zero have
the same Dirichlet density, or neither has one. In particular the Dirichlet density of a set of
primes does not change when finitely many primes are added or removed, or when the set is
restricted to the primes of residue degree one.

## Main results

* `NumberField.Set.hasDirichletDensity_zero_of_eventually_le`: a set whose partial sum is bounded
  as `s → 1⁺` has Dirichlet density zero.
* `NumberField.Set.hasDirichletDensity_zero_of_summable`: a set of primes with
  `∑_{𝔭 ∈ S} N(𝔭)⁻¹ < ∞` has Dirichlet density zero.
* `NumberField.Set.hasDirichletDensity_of_finite`: a finite set of primes has Dirichlet density
  zero, so a set of nonzero Dirichlet density is infinite
  (`NumberField.Set.HasDirichletDensity.infinite`).
* `NumberField.Set.hasDirichletDensity_iff_of_symmDiff`: sets whose symmetric difference has
  density zero have the same densities; `NumberField.Set.hasDirichletDensity_iff_of_finite_symmDiff`
  is the case of a finite symmetric difference.
* `TauCeti.hasDirichletDensity_higherDegreePrimes`: the primes of residue degree greater than one
  have Dirichlet density zero, and
  `TauCeti.hasDirichletDensity_inter_compl_higherDegreePrimes_iff` lets a density be computed on
  the primes of residue degree one alone.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.1.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

 section

namespace NumberField.Set

open _root_.Filter _root_.IsDedekindDomain _root_.NumberField _root_.TauCeti
open scoped _root_.NumberField _root_.TauCeti.NumberField _root_.symmDiff _root_.Topology

variable {K : Type*} [Field K] [NumberField K]
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}

/-- **A bounded partial sum gives density zero.** If `P_S(s) ≤ C` for all `s` close enough to `1`
from the right, then `S` has Dirichlet density zero, because the all-prime denominator tends to
infinity. -/
theorem hasDirichletDensity_zero_of_eventually_le {C : ℝ}
    (h : ∀ᶠ s in 𝓝[>] (1 : ℝ), S.primeIdealZetaSum s ≤ C) : S.HasDirichletDensity 0 := by
  have hP := tendsto_primeIdealZetaSum_univ_atTop (K := K)
  refine hasDirichletDensity_iff.2 <| tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds ((tendsto_const_nhds (x := C)).div_atTop hP) ?_ ?_
  · filter_upwards with s
    exact div_nonneg (S.primeIdealZetaSum_nonneg s) (Set.univ.primeIdealZetaSum_nonneg s)
  · filter_upwards [h, hP.eventually_gt_atTop 0] with s hs hpos
    exact div_le_div_of_nonneg_right hs hpos.le



/-- **Finite sets of primes have Dirichlet density zero.** -/
theorem hasDirichletDensity_of_finite (hS : S.Finite) : S.HasDirichletDensity 0 := by
  refine hasDirichletDensity_zero_of_eventually_le (C := S.ncard) ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  exact primeIdealZetaSum_le_card_of_finite hS (by linarith)











/-- **Finite changes do not affect Dirichlet density.** If `T` has Dirichlet density `δ` and `S`
differs from `T` in finitely many primes, then `S` has Dirichlet density `δ`. -/
theorem HasDirichletDensity.of_finite_symmDiff (hT : T.HasDirichletDensity δ)
    (hST : (S ∆ T).Finite) : S.HasDirichletDensity δ :=
  hT.of_symmDiff (hasDirichletDensity_of_finite hST)



end NumberField.Set

open _root_.IsDedekindDomain _root_.NumberField _root_.NumberField.Set

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]







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
# A counting criterion for a prime to split completely in a number field

For a finite Galois number field `K / ℚ`, a rational prime `p` splits completely — meaning
there are exactly `[K : ℚ]` primes of `𝓞 K` above `p` — if and only if `p` is unramified with
residue degree one, i.e. both the ramification index `e` and the inertia degree `f` (which are
common to all primes above `p`, the extension being Galois) equal `1`.

One direction needs no Galois hypothesis at all: a full complement of primes already forces
`e = f = 1` at each of them, directly from the fundamental identity, and hence identifies each
residue field with the prime field.

This is the count form of the fundamental identity `(#primes) · e · f = [L : K]`: with the
product fixed at `[L : K]`, the number of primes is maximal exactly when `e = f = 1`. The
rational-prime corollary is the Galois-number-field criterion underlying the multiquadratic
prime-splitting law (Layer 1 of the multiquadratic roadmap), where complete splitting is read
off from residues.

## Main results

* `NumberField.ncard_primesOver_eq_finrank_iff_of_isGalois`: the relative criterion over an
  arbitrary Dedekind base.
* `NumberField.ncard_primesOver_eq_finrank_iff`: the rational-prime specialization.
* `NumberField.bijective_algebraMap_quotient_of_ncard_primesOver_eq_finrank`:
  complete splitting makes each residue field the prime field.
* `Ideal.absNorm_eq_of_ncard_primesOver_eq_finrank`: a prime above a completely split
  rational prime has that prime as its absolute norm.
* `NumberField.ncard_primesOver_eq_finrank_iff_stabilizer_eq_bot`: the orbit–stabilizer
  form — `p` splits completely iff the decomposition group of a prime above it is trivial.

## Provenance

Two of Mathlib's fundamental identities are used, according to whether a Galois hypothesis is
available. The splitting criterion itself rests on the Galois identity
(`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`). The consequences drawn without
a Galois hypothesis — that complete splitting forces `e = f = 1`, and hence that the residue field
at `Q` is the prime field — rest instead on the general identity for finite flat extensions of
domains (`Ideal.sum_ramification_inertia_eq_finrank`), applied through
the general theorem in `TauCeti.RamificationInertia.Splitting`.
The criterion is assembled here for the Tau Ceti library.
-/

 section

open _root_.NumberField _root_.Ideal _root_.Module _root_.MulAction
open scoped _root_.Pointwise

namespace NumberField

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- In a Galois extension of number fields, the number of primes over a maximal ideal of a
Dedekind base equals the relative degree iff the common ramification index and inertia degree
are both `1`. -/
theorem ncard_primesOver_eq_finrank_iff_of_isGalois {A : Type*} [CommRing A]
    [IsDedekindDomain A] [Algebra A (𝓞 L)] [Module.Finite A (𝓞 L)]
    [IsTorsionFree A (𝓞 L)] [IsGaloisGroup Gal(L/K) A (𝓞 L)] (P : Ideal A) [P.IsMaximal] :
    (primesOver P (𝓞 L)).ncard = finrank K L ↔
      P.ramificationIdxIn (𝓞 L) = 1 ∧ P.inertiaDegIn (𝓞 L) = 1 := by
  have h := TauCeti.RamificationInertia.ncard_primesOver_eq_natCard_iff_of_isGaloisGroup
    (B := 𝓞 L) Gal(L/K) P
  rw [IsGaloisGroup.card_eq_finrank Gal(L/K) K L] at h
  exact h





open TauCeti.RamificationInertia in
/-- **A full complement of primes forces unramifiedness.** If `𝓞 L` has `[L : K]` primes above a
maximal ideal `𝔭` of `𝓞 K`, then every prime `Q` of `𝓞 L` above `𝔭` is unramified over `𝓞 K`.
No Galois hypothesis is needed. -/
theorem isUnramifiedAt_of_ncard_primesOver_eq_finrank {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hsplit : (primesOver 𝔭 (𝓞 L)).ncard = finrank K L) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver 𝔭] : Algebra.IsUnramifiedAt (𝓞 K) Q := by
  have : (Q.under (𝓞 K)).IsMaximal := by
    rw [← Ideal.over_def Q 𝔭]
    infer_instance
  -- The fundamental identity `∑ e f = [L : K]` leaves no room for `e > 1` once the primes above
  -- `𝔭` already number the rank; that count is taken over the rings, so the degree of the field
  -- extension has to be transported down to `𝓞 L` over `𝓞 K` first.
  rw [← Ideal.ramificationIdx_eq_one_iff]
  exact (ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank 𝔭 Q
    (by rwa [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L] at hsplit)).1



end NumberField

namespace Ideal



end Ideal

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
# The Artin symbol of an unramified prime

For a finite Galois extension of number fields, this file attaches to an unramified
prime ideal of the base the conjugacy class of its arithmetic Frobenius elements.
The definition uses Mathlib's `IsArithFrobAt` and `arithFrobAt`; no Frobenius
predicate or representative is introduced here.

The construction follows Jürgen Neukirch, *Algebraic Number Theory*, Chapter I, §9,
Exercise 2.

The same reference gives functoriality in a normal tower: restriction maps the Artin symbol of
`L/K` to the Artin symbol of `M/K`. Unramifiedness in the intermediate extension is derived from
unramifiedness in the top extension, rather than assumed separately.

Raising the base field is the companion law, and it takes a power: for `K ⊆ M ⊆ L`, the symbol
of a prime of `𝓞 M` above `𝔭`, read inside `Gal(L/K)`, is the `f(𝔓/𝔭)`-th power of the symbol of
`𝔭`. Stated on conjugacy classes it names no prime of `𝓞 L` and no Frobenius representative, both
of which the element-level form in `TauCeti.NumberTheory.NumberField.Frobenius.Tower` fixes.

Finally, the symbol detects complete splitting: it is the identity class exactly when the
residue degree is one, equivalently when `𝓞 L` has `[L : K]` primes above `𝔭`.
-/

 section

open _root_.Ideal
open scoped _root_.NumberField _root_.Pointwise

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]









section IsoOfExtensions

/-!
### Transport along an isomorphism of extensions

An isomorphism `e : L ≃ₐ[K] L'` of extensions of `K` induces `𝓞 L ≃ₐ[𝓞 K] 𝓞 L'`, and everything
`artinSymbol` is built from travels along it: the primes above `𝔭`, their unramifiedness, and the
Frobenius condition. The symbol itself is therefore equivariant for the induced isomorphism
`AlgEquiv.autCongr e` of Galois groups.
-/

variable {L L' : Type*} [Field L] [Algebra K L] [Field L'] [Algebra K L']

variable [NumberField L] [IsGalois K L] [NumberField L'] [IsGalois K L']



end IsoOfExtensions

section SplitsCompletely

/-!
### The trivial Artin symbol

Two equivalent readings of the identity Artin class at an unramified prime: residue degree one,
and complete splitting.
-/

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- **The Artin symbol is trivial exactly at residue degree one.** For a prime `Q` of `𝓞 L` above
an unramified `𝔭`, the Artin symbol of `𝔭` is the identity class if and only if `f(Q/𝔭) = 1`.

The residue degree is common to all primes above `𝔭`, so the choice of `Q` is immaterial. -/
theorem artinSymbol_eq_one_iff_inertiaDeg_eq_one (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭], Algebra.IsUnramifiedAt (𝓞 K) Q)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭] :
    artinSymbol 𝔭 hur = 1 ↔ Q.inertiaDeg (𝓞 K) = 1 := by
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (NeZero.ne 𝔭) Q
  have : Algebra.IsUnramifiedAt (𝓞 K) Q := hur Q
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q hQ
  rw [artinSymbol_eq_mk_of_isArithFrobAt 𝔭 hur Q σ hσ, ConjClasses.one_eq_mk_one,
    ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left, ← orderOf_eq_one_iff,
    orderOf_eq_inertiaDeg_of_isArithFrobAt Q hQ hσ]

/-- **The Artin symbol is trivial exactly at the completely split primes.** For `𝔭` unramified in
`L`, the Artin symbol of `𝔭` is the identity class if and only if `𝔭` splits completely, that is,
`𝓞 L` has `[L : K]` primes above `𝔭`.

A caller who knows the prime count therefore knows the symbol, and conversely. -/
theorem artinSymbol_eq_one_iff_ncard_primesOver_eq_finrank (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭], Algebra.IsUnramifiedAt (𝓞 K) Q) :
    artinSymbol 𝔭 hur = 1 ↔ (𝔭.primesOver (𝓞 L)).ncard = Module.finrank K L := by
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (𝔭.primesOver (𝓞 L)))
  have : Algebra.IsUnramifiedAt (𝓞 K) Q := hur Q
  rw [artinSymbol_eq_one_iff_inertiaDeg_eq_one 𝔭 hur Q,
    ncard_primesOver_eq_finrank_iff_of_isGalois K L 𝔭,
    Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭 Q (L ≃ₐ[K] L),
    Ideal.inertiaDegIn_eq_inertiaDeg 𝔭 Q (L ≃ₐ[K] L),
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt]
  exact (and_iff_right rfl).symm

end SplitsCompletely

section BaseChange

/-!
### Raising the base field

The companion to `artinSymbol_map_restrictNormalHom`. That law shrinks the top field of a normal
tower and takes no power; this one raises the base field and takes the power `f(𝔓/𝔭)`.
-/

-- Source. Both transport laws are specified by `TauCetiRoadmap/Chebotarev/README.md` Layer 1,
-- which asks for closed transport lemmas derived from `artinSymbol_map_restrictNormalHom` and
-- `exists_isArithFrobAt_pow_inertiaDeg`. This is the second of the two.



end BaseChange

end NumberField

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
# The unramified primes carrying a prescribed Artin class

Let `L / K` be a finite Galois extension of number fields and let `C` be a conjugacy class in
`Gal(L/K)`. This file defines the set

`frobeniusPrimeSet K L C : Set (HeightOneSpectrum (𝓞 K))`

of height-one primes `𝔭` of `𝓞 K` that are unramified in `L` and whose Artin class is `C`. It is
the set whose density the Chebotarev density theorem computes.

## The dependent membership condition

`artinSymbol` is a *partial* construction: it takes an unramifiedness proof as an argument and has
no value at a ramified prime. So membership cannot be an equation between two total functions;
it is stated as

`∃ hur : (𝔭 is unramified in L), artinSymbol 𝔭.asIdeal hur = C`,

an existential over a proof. Membership is nonetheless unambiguous: it does not depend on which
unramifiedness proof witnesses it, and `mem_frobeniusPrimeSet_iff_artinSymbol_eq` turns the
existential into the plain equation `artinSymbol 𝔭.asIdeal hur = C` for whichever unramifiedness
proof `hur` the caller has in hand.

The alternative — a total `Gal(L/K)`-valued or `ConjClasses`-valued function taking a junk value
at the ramified primes — is worse for this set: the junk value carries no arithmetic content, yet
the ramified primes would sit inside the fibre of whichever class it names, so the fibres would
neither cover the unramified primes exactly nor be pinned down by a Frobenius element there. The
existential is what keeps the fibres free of them.

## Main definitions

* `NumberField.Chebotarev.frobeniusPrimeSet`: the primes of `𝓞 K` unramified in `L` whose Artin
  class is `C`.

## Main results

* `NumberField.Chebotarev.mem_frobeniusPrimeSet_iff_artinSymbol_eq`: proof-independence — with
  any unramifiedness proof in hand, membership is the equation `artinSymbol 𝔭.asIdeal hur = C`.
* `NumberField.Chebotarev.mem_frobeniusPrimeSet_mk_iff_exists_isArithFrobAt`: for an unramified
  `𝔭` and an element `σ`, membership in the fibre of `[σ]` says exactly that `σ` is an arithmetic
  Frobenius at *some* prime of `𝓞 L` above `𝔭`.
* `NumberField.Chebotarev.frobeniusPrimeSet_map_autCongr`: equivariance — an isomorphism
  `e : L ≃ₐ[K] L'` of extensions of `K` matches the fibre of `C` in `L` with the fibre in `L'` of
  the image of `C` under the induced isomorphism `AlgEquiv.autCongr e` of Galois groups.
* `NumberField.Chebotarev.frobeniusPrimeSet_subset_map_restrictNormalHom`: a fibre over `L` lies
  in the fibre over a Galois subextension `M` of the restricted class.
* `NumberField.Chebotarev.disjoint_frobeniusPrimeSet`: distinct classes have disjoint fibres.
* `NumberField.Chebotarev.iUnion_frobeniusPrimeSet`: the fibres cover exactly the complement of
  `ramifiedPrimes K L`, so `existsUnique_mem_frobeniusPrimeSet` partitions the unramified primes
  and `finite_compl_iUnion_frobeniusPrimeSet` records that the discarded remainder is finite.

The last two are what let the density arguments discard a finite exceptional set and then work
one class at a time: a lower density bound for each class can be squeezed against a partition of
a cofinite set, which is how the crossing argument produces exact densities.
-/

 section

open _root_.Ideal
open scoped _root_.NumberField

open _root_.IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]



/-- Membership in `frobeniusPrimeSet`, unfolded. Downstream files should open the definition
through this lemma rather than through defeq. -/
@[simp]
theorem mem_frobeniusPrimeSet_iff {𝔭 : HeightOneSpectrum (𝓞 K)}
    {C : ConjClasses (L ≃ₐ[K] L)} :
    𝔭 ∈ frobeniusPrimeSet K L C ↔
      ∃ hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
        Algebra.IsUnramifiedAt (𝓞 K) Q, artinSymbol 𝔭.asIdeal hur = C :=
  Iff.rfl



/-- **Proof-independence.** Once an unramifiedness proof `hur` is available, membership in
`frobeniusPrimeSet K L C` is the plain equation `artinSymbol 𝔭.asIdeal hur = C`: the existential
in the definition may be instantiated at `hur`, whatever proof it was introduced with.

Membership in `frobeniusPrimeSet K L C` is therefore independent of the unramifiedness proof used
to test it. -/
theorem mem_frobeniusPrimeSet_iff_artinSymbol_eq {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) (C : ConjClasses (L ≃ₐ[K] L)) :
    𝔭 ∈ frobeniusPrimeSet K L C ↔ artinSymbol 𝔭.asIdeal hur = C :=
  ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hur, h⟩⟩



/-- A member of `frobeniusPrimeSet K L C` is unramified in `L`. -/
theorem isUnramifiedAt_of_mem_frobeniusPrimeSet {𝔭 : HeightOneSpectrum (𝓞 K)}
    {C : ConjClasses (L ≃ₐ[K] L)} (h : 𝔭 ∈ frobeniusPrimeSet K L C)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 K) Q :=
  (mem_frobeniusPrimeSet_iff.mp h).elim fun hur _ ↦ hur Q



/-- **A Frobenius witnesses membership.** If `σ` is an arithmetic Frobenius at a prime `Q` of
`𝓞 L` above an unramified `𝔭`, then `𝔭` lies in the fibre of the class of `σ`. -/
theorem mem_frobeniusPrimeSet_mk_of_isArithFrobAt {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    𝔭 ∈ frobeniusPrimeSet K L (ConjClasses.mk σ) :=
  ⟨hur, artinSymbol_eq_mk_of_isArithFrobAt 𝔭.asIdeal hur Q σ hσ⟩





section IsoOfExtensions

variable {L' : Type*} [Field L'] [NumberField L'] [Algebra K L'] [IsGalois K L']



end IsoOfExtensions

section RestrictNormal

variable {M : Type*} [Field M] [NumberField M] [Algebra K M] [Algebra M L] [IsScalarTower K M L]
  [IsGalois K M]

/-- **Fibres shrink along restriction to a normal subextension.** For a tower `L / M / K` with
`M / K` Galois, a prime in the fibre of `C` over `L` lies in the fibre over `M` of the restriction
of `C`. Unramifiedness in `M` is part of the conclusion, not a hypothesis.

This is `artinSymbol_map_restrictNormalHom` read on fibres: restriction takes no power. -/
theorem frobeniusPrimeSet_subset_map_restrictNormalHom (C : ConjClasses (L ≃ₐ[K] L)) :
    frobeniusPrimeSet K L C ⊆
      frobeniusPrimeSet K M (ConjClasses.map (AlgEquiv.restrictNormalHom M) C) := by
  rintro 𝔭 ⟨hur, rfl⟩
  exact ⟨_, (artinSymbol_map_restrictNormalHom 𝔭.asIdeal hur).symm⟩

end RestrictNormal











end NumberField.Chebotarev

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
# The completely split primes as the identity Artin fibre

Let `L / K` be a finite Galois extension of number fields. Among the fibres of the Artin class
studied in `TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet`, the fibre of the identity class
`1` is distinguished: it consists exactly of the primes of `𝓞 K` that split completely in `L`.

Two readings of membership in `frobeniusPrimeSet K L 1` are recorded. The residue-degree reading
asks for a prime `𝔭` unramified in `L`, and says that `f(Q/𝔭)` is `1` at one — hence, since
`L / K` is Galois, at every — prime `Q` of `𝓞 L` above `𝔭`. The counting reading needs no
hypothesis at all: `𝔭` carries the identity Artin class exactly when `𝓞 L` has the full
complement of `[L : K]` primes above `𝔭`.

That asymmetry is the point of the file. A full complement of primes above `𝔭` already forces
the ramification index at every prime above `𝔭` to be `1`, hence forces `𝔭` to be unramified —
that is `NumberField.isUnramifiedAt_of_ncard_primesOver_eq_finrank`, in
`TauCeti.NumberTheory.NumberField.SplitsCompletely.Basic`. So the counting characterization and its
set-level corollary both stand unconditionally, and `frobeniusPrimeSet K L 1` is the set of
completely split primes on the nose, with no finite exceptional set to discard.

## Main results

* `NumberField.Chebotarev.mem_frobeniusPrimeSet_one_iff_inertiaDeg_eq_one`: for `𝔭` unramified
  in `L`, membership in the identity fibre is residue degree one at a prime above `𝔭`.
* `NumberField.Chebotarev.mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank`: the same
  membership, read as a count of the primes above `𝔭`.
* `NumberField.Chebotarev.inertiaDeg_eq_one_of_mem_frobeniusPrimeSet_one`: a member of the
  identity fibre has residue degree one at *every* prime above it.
* `NumberField.Chebotarev.frobeniusPrimeSet_one_eq_setOf_ncard_primesOver_eq_finrank`: as a set,
  the identity fibre is the primes of `𝓞 K` with `[L : K]` primes of `𝓞 L` above them.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9, where the Frobenius at an unramified
  prime is trivial exactly when that prime splits completely.
-/

 section

open _root_.Ideal
open scoped _root_.NumberField

open _root_.IsDedekindDomain (HeightOneSpectrum)

namespace NumberField


variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

namespace Chebotarev

/-- **The identity fibre is residue degree one.** For `𝔭` unramified in `L` and `Q` a prime of
`𝓞 L` above `𝔭`, the prime `𝔭` carries the identity Artin class exactly when `f(Q/𝔭) = 1`.

The residue degree is common to all primes above `𝔭`, so the choice of `Q` is immaterial; see
`inertiaDeg_eq_one_of_mem_frobeniusPrimeSet_one`. -/
theorem mem_frobeniusPrimeSet_one_iff_inertiaDeg_eq_one {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
    𝔭 ∈ frobeniusPrimeSet K L 1 ↔ Q.inertiaDeg (𝓞 K) = 1 :=
  (mem_frobeniusPrimeSet_iff_artinSymbol_eq hur 1).trans
    (artinSymbol_eq_one_iff_inertiaDeg_eq_one 𝔭.asIdeal hur Q)

-- The conditional form, kept private: it is the direct specialisation of the general fibre
-- description, which carries an unramifiedness hypothesis, and the unconditional statement
-- below is derived from it by supplying that witness from each side of the iff.
private theorem mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank_of_isUnramified
    {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    𝔭 ∈ frobeniusPrimeSet K L 1 ↔ (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L :=
  (mem_frobeniusPrimeSet_iff_artinSymbol_eq hur 1).trans
    (artinSymbol_eq_one_iff_ncard_primesOver_eq_finrank 𝔭.asIdeal hur)

/-- **The identity fibre is complete splitting.** A height-one prime of `𝓞 K` carries the
identity Artin class in `L` exactly when `𝓞 L` has `[L : K]` primes above it.

No unramifiedness hypothesis is needed: complete splitting already implies it, so requiring it
separately would be redundant. -/
-- Deliberately not `@[simp]`: `mem_frobeniusPrimeSet_iff` is already `@[simp]` and rewrites this
-- left-hand side to the existential over an unramifiedness witness first, so the tag would leave
-- this out of simp-normal form and fail `simpNF`.
theorem mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank
    {𝔭 : HeightOneSpectrum (𝓞 K)} :
    𝔭 ∈ frobeniusPrimeSet K L 1 ↔ (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L :=
  ⟨fun h ↦ (mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank_of_isUnramified
      (isUnramifiedAt_of_mem_frobeniusPrimeSet h)).mp h,
    fun hcard ↦ (mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank_of_isUnramified
      (isUnramifiedAt_of_ncard_primesOver_eq_finrank 𝔭.asIdeal hcard)).mpr hcard⟩

/-- **Residue degree one at every prime above.** A member of the identity fibre has residue
degree `1` at each prime of `𝓞 L` lying over it, not merely at one of them. -/
theorem inertiaDeg_eq_one_of_mem_frobeniusPrimeSet_one {𝔭 : HeightOneSpectrum (𝓞 K)}
    (h : 𝔭 ∈ frobeniusPrimeSet K L 1) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
    Q.inertiaDeg (𝓞 K) = 1 :=
  (mem_frobeniusPrimeSet_one_iff_inertiaDeg_eq_one
    (isUnramifiedAt_of_mem_frobeniusPrimeSet h) Q).mp h



end Chebotarev

end NumberField

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
# The completely split primes have density `1 / [L : K]`

Let `L / K` be a finite Galois extension of number fields. The primes of `𝓞 K` that split
completely in `L` — the identity fibre `frobeniusPrimeSet K L 1` of the Artin class — have
Dirichlet density `1 / [L : K]`.

For an extension `E / K` that need not be Galois, a prime of `𝓞 K` splits completely in `E` exactly
when it splits completely in the Galois closure `N` of `E / K`, so the primes splitting completely
in `E` have Dirichlet density `1 / [N : K]`. Here `E` is an intermediate field of a finite Galois
extension `M / K`, and `N` is its normal closure in `M`.

## Main results

* `NumberField.Chebotarev.hasDirichletDensity_frobeniusPrimeSet_one`: the completely split primes
  have Dirichlet density `1 / [L : K]`.
* `NumberField.Chebotarev.hasDirichletDensity_setOf_ncard_primesOver_eq_finrank`: the primes
  splitting completely in an intermediate field `E` of `M / K` have Dirichlet density `1 / [N : K]`,
  for `N` the normal closure of `E` in `M`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

 section

open _root_.IsDedekindDomain (HeightOneSpectrum)

open _root_.NumberField

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

private theorem under_mem_frobeniusPrimeSet_one_of_inertiaDeg_eq_one {𝔓 : HeightOneSpectrum (𝓞 L)}
    (hdeg : 𝔓.asIdeal.inertiaDeg (𝓞 K) = 1) (hram : 𝔓.under (𝓞 K) ∉ ramifiedPrimes K L) :
    𝔓.under (𝓞 K) ∈ frobeniusPrimeSet K L 1 := by
  have : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 K)).asIdeal := ⟨HeightOneSpectrum.under_asIdeal _ 𝔓⟩
  rw [mem_ramifiedPrimes_iff, not_not] at hram
  exact (mem_frobeniusPrimeSet_one_iff_inertiaDeg_eq_one hram 𝔓.asIdeal).mpr hdeg

private theorem card_inertiaDeg_eq_one_fiber_of_mem_frobeniusPrimeSet_one
    {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : 𝔭 ∈ frobeniusPrimeSet K L 1) :
    Nat.card {𝔓 : HeightOneSpectrum (𝓞 L) // 𝔓.under (𝓞 K) = 𝔭 ∧ 𝔓.asIdeal.inertiaDeg (𝓞 K) = 1} =
      Module.finrank K L := by
  -- Over a completely split prime every prime above has residue degree one, and there are
  -- `[L : K]` of them.
  have hdiv (𝔓 : HeightOneSpectrum (𝓞 L)) :
      (𝔓.under (𝓞 K) = 𝔭 ∧ 𝔓.asIdeal.inertiaDeg (𝓞 K) = 1) ↔
        𝔓.asIdeal ∣ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔭.asIdeal := by
    rw [← Ideal.liesOver_iff_dvd_map 𝔓.isPrime.ne_top]
    refine ⟨fun h ↦ ⟨(congrArg HeightOneSpectrum.asIdeal h.1).symm⟩, fun h ↦ ?_⟩
    obtain rfl : 𝔓.under (𝓞 K) = 𝔭 := HeightOneSpectrum.ext h.over.symm
    exact ⟨rfl, inertiaDeg_eq_one_of_mem_frobeniusPrimeSet_one h𝔭 𝔓.asIdeal⟩
  rw [Nat.card_congr ((Equiv.subtypeEquivRight hdiv).trans
    (HeightOneSpectrum.equivPrimesOver (𝓞 L) 𝔭.ne_bot)), Nat.card_coe_set_eq]
  exact mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank.mp h𝔭

variable (K L) in
/-- **The completely split primes have density `1 / [L : K]`.** The primes of `𝓞 K` that split
completely in the finite Galois extension `L` have Dirichlet density `1 / [L : K]`. The
Chebotarev density theorem gives the same density as `1 / #Gal(L/K)`
(`hasDirichletDensity_splitCompletely`). -/
theorem hasDirichletDensity_frobeniusPrimeSet_one :
    (frobeniusPrimeSet K L 1).HasDirichletDensity (1 / Module.finrank K L) :=
  -- Contract all the primes of `𝓞 L`, which have density one: away from the ramified primes, a
  -- prime of residue degree one over `K` lies over a completely split prime, and each completely
  -- split prime has `[L : K]` primes above it.
  (Set.hasDirichletDensity_contraction (T := Set.univ)
    (Set.hasDirichletDensity_of_finite (K := K) (ramifiedPrimes K L).finite_toSet)
    (fun _ _ ↦ under_mem_frobeniusPrimeSet_one_of_inertiaDeg_eq_one) Module.finrank_pos.ne'
    fun _ h𝔭 ↦ by simpa using card_inertiaDeg_eq_one_fiber_of_mem_frobeniusPrimeSet_one h𝔭.1).mp
      Set.hasDirichletDensity_univ



end NumberField.Chebotarev

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
# The ray class group of a modulus

Let `𝔪` be a modulus of a number field `K`.  The **ray** of `𝔪` is the subgroup of principal
fractional ideals generated by the elements of `Kˣ` congruent to one modulo `𝔪`, and the **ray
class group** `RayClassGroup 𝔪` is the quotient of the group `idealsPrimeTo 𝔪` of invertible
fractional ideals prime to the finite part of `𝔪` by that ray.

The ray really is a subgroup of `idealsPrimeTo 𝔪`, and not merely of all invertible fractional
ideals: an element congruent to one is a unit at every prime dividing the finite part of `𝔪`
(`IsCongrOne.valuation_eq_one`), so its principal ideal has vanishing multiplicity there.  That is
the content of `TauCeti.GlobalNumberFields.rayHom`, from which the ray is obtained as a range.

The class of an ideal is defined on the monoid `integralIdealsPrimeTo 𝔪` of nonzero integral ideals
prime to the finite part, never on all of `Ideal (𝓞 K)`: an ideal sharing a prime with the finite
part has no ray class, and carrying the coprimality proof in the argument makes multiplicativity
literally `map_mul`.

For the trivial modulus the congruence condition is empty, and the ray class group is the ordinary
class group (`oneEquivClassGroup`).

## Main definitions

* `TauCeti.GlobalNumberFields.principalIdealPrimeTo`: the principal fractional ideals whose
  generators are units at the finite part.
* `TauCeti.GlobalNumberFields.rayHom`, `TauCeti.GlobalNumberFields.ray`: the principal ideals of
  the elements congruent to one, and the subgroup they form.
* `TauCeti.GlobalNumberFields.idealsPrimeToClassGroup`: the ordinary ideal class of an invertible
  fractional ideal prime to a modulus.
* `TauCeti.GlobalNumberFields.RayClassGroup`: the quotient of `idealsPrimeTo 𝔪` by the ray, with
  `TauCeti.GlobalNumberFields.rayClassMk` and the universal property
  `TauCeti.GlobalNumberFields.rayClassLift`.
* `TauCeti.GlobalNumberFields.idealClass`: the ray class of an integral ideal prime to `𝔪`, as a
  monoid homomorphism out of `integralIdealsPrimeTo 𝔪`.
* `TauCeti.GlobalNumberFields.classMap`: the transition map, running from the ray class group of a
  larger modulus to that of a divisor of it.

## Main results

* `TauCeti.GlobalNumberFields.toPrincipalIdeal_mem_idealsPrimeTo_iff`: a principal fractional ideal
  is prime to the modulus exactly when its generator is a unit at every prime dividing the finite
  part, with `TauCeti.GlobalNumberFields.IsCongrOne.toPrincipalIdeal_mem_idealsPrimeTo` the
  consequence for an element congruent to one.
* `TauCeti.GlobalNumberFields.idealsPrimeTo_eq_top`: every invertible fractional ideal is prime
  to a modulus whose support is empty, so `TauCeti.GlobalNumberFields.idealsPrimeToEquiv`
  identifies the two carriers there.
* `TauCeti.GlobalNumberFields.idealClass_apply`: the ray class of an integral ideal is the ray
  class of the fractional ideal it generates.
* `TauCeti.GlobalNumberFields.idealClass_mul`: taking the ray class of an integral ideal respects
  multiplication.
* `TauCeti.GlobalNumberFields.idealClass_eq_one_iff`: an ideal has trivial ray class exactly when
  it is generated, as a fractional ideal, by an element of `Kˣ` congruent to one modulo `𝔪`.
* `TauCeti.GlobalNumberFields.classMap_comp_classMap` and
  `TauCeti.GlobalNumberFields.classMap_comp_idealClass`: the transition maps compose along a tower
  of moduli, and carry the class of an integral ideal to the class of the same ideal.  Both are
  equalities of homomorphisms, with the pointwise forms `classMap_classMap` and
  `classMap_idealClass` derived from them.  The transition map from a modulus to itself is the
  identity (`TauCeti.GlobalNumberFields.classMap_refl`).
* `TauCeti.GlobalNumberFields.oneEquivClassGroup`: at the trivial modulus the ray class group is
  the class group of `𝓞 K`, carrying a ray class to the class of the same fractional ideal
  (`TauCeti.GlobalNumberFields.oneEquivClassGroup_rayClassMk`).

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

 section

open _root_.IsDedekindDomain _root_.IsDedekindDomain.HeightOneSpectrum _root_.NumberField
open scoped _root_.nonZeroDivisors _root_.NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]





































@[simp] theorem rayClassLift_rayClassMk {M : Type*} [Monoid M] {𝔪 : Modulus K}
    (φ : idealsPrimeTo 𝔪 →* M) (h : ray 𝔪 ≤ φ.ker) (I : idealsPrimeTo 𝔪) :
    rayClassLift φ h (rayClassMk 𝔪 I) = φ I := (rfl)









/-- The ray class of an integral ideal is the ray class of the fractional ideal it generates. -/
theorem idealClass_apply (𝔪 : Modulus K) (I : integralIdealsPrimeTo 𝔪) :
    idealClass 𝔪 I = rayClassMk 𝔪 (NumberFieldArithmetic.integralIdealsAwayHom 𝔪.support I) :=
  (rfl)



/-! ### The transition map between ray class groups -/

















/-! ### Moduli with unit finite part -/









/-! ### The trivial modulus -/







end TauCeti.GlobalNumberFields

end
end

section
set_option autoImplicit true
namespace TauCeti.GlobalNumberFields
end TauCeti.GlobalNumberFields
namespace TauCeti.NumberFieldArithmetic
end TauCeti.NumberFieldArithmetic
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Cyclotomic Galois characters as ray class characters

Let `F = K(μ_m)` be an `m`-th cyclotomic extension of a number field `K`, and let `𝔪` be the
modulus of `K` with finite part `(m)` and every real place in its infinite part. This file
provides the Artin map of the abelian extension `F / K` as a homomorphism from the ray class group
of `𝔪` to `Gal(F/K)`. It sends the ray class of a prime `𝔭 ∤ m` to the Frobenius at `𝔭`.

Composing with it, every character `χ` of `Gal(F/K)` gives a ray class character of `𝔪`, and on
the integral ideals prime to `m` the ideal weight `galoisCharacterWeight χ` of `χ` agrees with that
ray class character.

## Main definitions

* `NumberField.Chebotarev.cyclotomicModulus`: the modulus of `K` with finite part `(m)` and
  every real place in its infinite part.
* `NumberField.Chebotarev.cyclotomicArtin`: the Artin map
  `RayClassGroup (cyclotomicModulus K m) →* (F ≃ₐ[K] F)`.

## Main results

* `NumberField.Chebotarev.cyclotomicArtin_idealClass_of_isArithFrobAt`: the Artin map sends the
  ray class of a prime `𝔭 ∤ m` to the Frobenius at `𝔭`.
* `MonoidHom.galoisCharacterWeight_eq_onIdeals_cyclotomicArtin`: on the integral ideals prime to
  `m`, the ideal weight of a character `χ` of `Gal(F/K)` is the ray class character
  `χ ∘ cyclotomicArtin`.
-/

 section

open _root_.IsDedekindDomain _root_.IsDedekindDomain.HeightOneSpectrum _root_.NumberField
open scoped _root_.nonZeroDivisors _root_.NumberField

namespace NumberField.Chebotarev

open _root_.TauCeti.GlobalNumberFields _root_.TauCeti.NumberFieldArithmetic

section Modulus

variable (K : Type*) [Field K] [NumberField K] (m : ℕ) [NeZero m]







variable {K m}





end Modulus

section Auxiliary

variable {K : Type*} [Field K] [NumberField K]

-- A nonzero integer congruent to one modulo `(m)` generates an ideal prime to the cyclotomic
-- modulus.


end Auxiliary

section Cyclotomic



variable {K : Type*} [Field K] [NumberField K] (F : Type*) [Field F] [NumberField F]
  [Algebra K F] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

-- The Artin map of `F / K` on the fractional ideals prime to `m`.


-- The Artin map of `F / K` on the integral ideals prime to `m`.


-- The integral Artin map is the fractional one read on the ideals the integral ones generate.


-- At a prime not dividing `m`, the integral Artin map is the Frobenius.


-- The cyclotomic character of the integral Artin map is the absolute norm.


-- The Artin map of `F / K` kills the ray of the cyclotomic modulus.




-- On the ray class of an integral ideal, `cyclotomicArtin` is the integral Artin map.
private theorem cyclotomicArtin_idealClass (I : integralIdealsPrimeTo (cyclotomicModulus K m)) :
    cyclotomicArtin K F m (idealClass _ I) = cyclotomicArtinIntegral F m I := by
  rw [idealClass_apply, cyclotomicArtin, rayClassLift_rayClassMk, cyclotomicArtinIntegral_apply]

/-- **The Artin map sends the ray class of a prime to its Frobenius.** At a height-one prime `𝔭`
not dividing `m`, every arithmetic Frobenius at every prime of `𝓞 F` above `𝔭` is the image of
the ray class of `𝔭`. -/
theorem cyclotomicArtin_idealClass_of_isArithFrobAt (𝔭 : HeightOneSpectrum (𝓞 K))
    (h𝔭 : 𝔭.asIdeal ∈ integralIdealsPrimeTo (cyclotomicModulus K m)) (Q : Ideal (𝓞 F)) [Q.IsPrime]
    [Q.LiesOver 𝔭.asIdeal] {σ : F ≃ₐ[K] F} (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    cyclotomicArtin K F m (idealClass _ ⟨𝔭.asIdeal, h𝔭⟩) = σ := by
  rw [cyclotomicArtin_idealClass, cyclotomicArtinIntegral_of_isArithFrobAt F m 𝔭 h𝔭 Q hσ]

end Cyclotomic

end NumberField.Chebotarev

namespace MonoidHom

open _root_.TauCeti.GlobalNumberFields _root_.TauCeti.NumberFieldArithmetic _root_.NumberField.Chebotarev
open scoped _root_.IsMulCommutative

variable {K : Type*} [Field K] [NumberField K] {F : Type*} [Field F] [NumberField F]
  [Algebra K F] {m : ℕ} [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

-- At a prime `v ∤ m`, the ideal weight of `χ` is `χ` of the Artin image of the ray class of `v`.




end MonoidHom

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
# Surjectivity of the cyclotomic Artin map

Let `F = K(μ_m)` be an `m`-th cyclotomic extension of a number field `K`. This file proves that
the Artin map `cyclotomicArtin K F m` from the ray class group of `cyclotomicModulus K m` to
`Gal(F/K)` is surjective.

## Main results

* `NumberField.Chebotarev.cyclotomicArtin_surjective`: the cyclotomic Artin map is surjective.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

 section

open IsDedekindDomain IntermediateField
open scoped symmDiff

namespace NumberField.Chebotarev
end NumberField.Chebotarev
section NumberField.Chebotarev
open NumberField NumberField.Chebotarev

variable (K : Type*) [Field K] [NumberField K] (F : Type*) [Field F] [NumberField F]
  [Algebra K F] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

-- Every prime `𝔭 ∤ m` has its Frobenius in the image of the Artin map, so it splits completely in
-- the fixed field of that image.
variable {K m} in
private theorem NumberField.Chebotarev.mem_frobeniusPrimeSet_fixedField_range_cyclotomicArtin
    [_root_.IsMulCommutative (F ≃ₐ[K] F)] {𝔭 : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)} (h𝔭 : (m : 𝓞 K) ∉ 𝔭.asIdeal) :
    𝔭 ∈ _root_.NumberField.Chebotarev.frobeniusPrimeSet K (_root_.IntermediateField.fixedField (_root_.NumberField.Chebotarev.cyclotomicArtin K F m).range) 1 := by
  have hmem := asIdeal_mem_integralIdealsPrimeTo_cyclotomicModulus_iff.mpr h𝔭
  obtain ⟨Q, _, _⟩ := (_root_.inferInstance : _root_.Nonempty (𝔭.asIdeal.primesOver (𝓞 F)))
  obtain ⟨σ, hσ⟩ := _root_.NumberField.exists_isArithFrobAt K Q (_root_.Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q)
  have hσH : _root_.AlgEquiv.restrictNormalHom (_root_.IntermediateField.fixedField (_root_.NumberField.Chebotarev.cyclotomicArtin K F m).range) σ = 1 := by
    rw [← _root_.MonoidHom.mem_ker, _root_.IntermediateField.restrictNormalHom_ker, _root_.IntermediateField.fixingSubgroup_fixedField]
    exact ⟨_, _root_.NumberField.Chebotarev.cyclotomicArtin_idealClass_of_isArithFrobAt F m 𝔭 hmem Q hσ⟩
  simpa only [_root_.ConjClasses.map_mk, hσH, ← _root_.ConjClasses.one_eq_mk_one] using
    _root_.NumberField.Chebotarev.frobeniusPrimeSet_subset_map_restrictNormalHom (M := _root_.IntermediateField.fixedField (_root_.NumberField.Chebotarev.cyclotomicArtin K F m).range) _
      (_root_.NumberField.Chebotarev.mem_frobeniusPrimeSet_mk_of_isArithFrobAt (fun Q _ _ ↦
        _root_.NumberField.Chebotarev.isUnramifiedAt_of_notMem_cyclotomicModulus_support F m
          (mem_cyclotomicModulus_support_iff.not.mpr h𝔭) Q) Q hσ)

/-- **The cyclotomic Artin map is surjective.** For `F = K(μ_m)`, every automorphism of `F / K` is
the Artin automorphism of a ray class of `cyclotomicModulus K m`. -/
theorem solution : _root_.Function.Surjective (_root_.NumberField.Chebotarev.cyclotomicArtin K F m) := by
  have := _root_.IsCyclotomicExtension.isMulCommutative {m} K F
  rw [← _root_.MonoidHom.range_eq_top]
  set H := (_root_.NumberField.Chebotarev.cyclotomicArtin K F m).range
  -- Every prime not dividing `m` splits completely in the fixed field of `H`, so the completely
  -- split primes of that field have density one; they also have density one over its degree, so
  -- the fixed field is `K` and `H` is the whole Galois group.
  have hfin : (_root_.NumberField.Chebotarev.frobeniusPrimeSet K (_root_.IntermediateField.fixedField H) 1 ∆ _root_.Set.univ).Finite := by
    refine (_root_.NumberField.Chebotarev.cyclotomicModulus K m).support.finite_toSet.subset fun 𝔭 h𝔭 ↦ _root_.by_contra fun h ↦ ?_
    rw [← _root_.Set.top_eq_univ, _root_.symmDiff_top] at h𝔭
    exact h𝔭 (_root_.NumberField.Chebotarev.mem_frobeniusPrimeSet_fixedField_range_cyclotomicArtin F
      (mem_cyclotomicModulus_support_iff.not.mp h))
  have hdeg := (_root_.NumberField.Chebotarev.hasDirichletDensity_frobeniusPrimeSet_one K (_root_.IntermediateField.fixedField H)).unique
    (Set.hasDirichletDensity_univ.of_finite_symmDiff hfin)
  rw [_root_.one_div, _root_.inv_eq_one, _root_.Nat.cast_eq_one, _root_.IntermediateField.finrank_eq_one_iff] at hdeg
  rw [← _root_.IntermediateField.fixingSubgroup_fixedField H, hdeg, _root_.IntermediateField.fixingSubgroup_bot]

end NumberField.Chebotarev

end
end
