-- Prove2me | solution 1 for NumberField.Chebotarev.cyclotomicCharacterSeriesC_ne_zero_at_one
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T22:17:13.134176+00:00
-- url     : https://prove2.me/submissions/d050e60c-72e7-414b-af5e-8b43e306d0ec

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Data_ZMod_Divisibility
import Definitions.Def_TauCeti_FieldTheory_Galois_Abelian
import Definitions.Def_TauCeti_GroupTheory_FiniteAbelian_CharacterOrthogonality
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Cancellation
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Estimates
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Analytic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Data
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Regroup
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Trivial
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_FrobeniusPrimeSet
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_GaloisCharacter_Cyclotomic_Basic
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_GaloisCharacter_Cyclotomic_Series
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_GaloisCharacter_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_RamifiedPrimes
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_NumberTheory_NumberField_Cyclotomic_Frobenius
import Definitions.Def_TauCeti_NumberTheory_NumberField_Cyclotomic_Ramification
import Definitions.Def_TauCeti_NumberTheory_NumberField_Frobenius
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Character_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Character_Sum
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Count_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Residue
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_ArtinMap
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_Away
import Definitions.Def_TauCeti_NumberTheory_NumberField_ResidueDegree
import Definitions.Def_TauCeti_NumberTheory_NumberField_TotallyPositive
import Definitions.Def_TauCeti_Order_Northcott_Basic
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
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
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
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
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
import Mathlib.Data.Set.Card.Arithmetic
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
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Complex
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
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_Complex_summable_taylorSeries_neg_log
import Theorems.Thm_NumberField_Chebotarev_cyclotomicArtin_surjective
import Theorems.Thm_NumberField_Set_hasDirichletDensity_contraction
import Theorems.Thm_NumberField_Set_hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one
import Theorems.Thm_Real_neg_log_one_sub_rpow_sub_le_div
import Theorems.Thm_Real_neg_log_one_sub_sub_le
import Theorems.Thm_TauCeti_EulerProductData_eulerFactor_eq_tsum
import Theorems.Thm_TauCeti_EulerProductData_hasProd_eulerFactor
import Theorems.Thm_TauCeti_GlobalNumberFields_isBigO_rayClassCharacterPartialSum
import Theorems.Thm_TauCeti_LSeriesSummable_normCoeff_one_iff
import Theorems.Thm_TauCeti_LSeries_differentiableOn_mul_integral_of_isBigO
import Theorems.Thm_TauCeti_MultiplicativeIdealWeight_LSeries_restrict
import Theorems.Thm_TauCeti_MultiplicativeIdealWeight_apply_ne_zero_iff_isGood
import Theorems.Thm_TauCeti_RamificationInertia_ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank
import Theorems.Thm_TauCeti_card_filter_rationalPrimeBelow_le_finrank
import Theorems.Thm_TauCeti_dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub
import Theorems.Thm_TauCeti_hasCancellation_iff_isBigO
import Theorems.Thm_TauCeti_idealCount_linearBounds
import Theorems.Thm_TauCeti_idealSummatory_eq_sum_range_normFiber
import Theorems.Thm_TauCeti_sum_norm_normCoeff_one
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
# The Taylor series of `-log (1 - ·)` summed over a family

Mathlib's `Complex.hasSum_taylorSeries_neg_log'` expands `-log (1 - z)` as `∑' e, z ^ (e+1)/(e+1)`
for a single `z` of modulus less than one.  This file sums that over a family `r : ι → ℂ`: the
double family indexed by `ι × ℕ` is summable, so the sum may be regrouped fibrewise and the
prime-power-style sum over pairs equals the sum of local logarithms.

Both hypotheses are needed.  `∀ i, ‖r i‖ < 1` alone does not suffice: the fibre at `i` sums to
`‖r i‖ / (1 - ‖r i‖)`, which is dominated by `‖r i‖` only when `‖r i‖` is bounded away from `1`,
and summability of `r` is what supplies that uniformity.  That fibrewise argument is not carried out
here: it is `TauCeti.summable_mul_norm_pow_succ`, stated for a seminormed additive group and an
arbitrary real weight, and this file uses it at weight `1`.

## Main results

* `Complex.summable_taylorSeries_neg_log`: for a summable `r : ι → ℂ` with every `‖r i‖ < 1`, the
  family `(i, e) ↦ r i ^ (e + 1) / (e + 1)` is summable over `ι × ℕ`.
* `Complex.tsum_taylorSeries_neg_log`: its sum over `ι × ℕ` is `∑' i, -log (1 - r i)`.
-/

 section

namespace Complex




/-- **The double sum is the sum of the local logarithms.**  For a summable `r : ι → ℂ` with every
`‖r i‖ < 1`, summing the Taylor series of `-log (1 - r i)` over `ι × ℕ` gives `∑' i, -log (1 - r i)`
— the fibrewise regrouping that `summable_taylorSeries_neg_log` licenses. -/
theorem tsum_taylorSeries_neg_log {ι : Type*} {r : ι → ℂ} (hr : Summable r)
    (h1 : ∀ i, ‖r i‖ < 1) :
    ∑' ie : ι × ℕ, r ie.1 ^ (ie.2 + 1) / ((ie.2 : ℂ) + 1) = ∑' i, -Complex.log (1 - r i) := by
  have hfib : ∀ i, HasSum (fun e : ℕ ↦ r i ^ (e + 1) / ((e : ℂ) + 1))
      (-Complex.log (1 - r i)) := fun i ↦ hasSum_taylorSeries_neg_log' (h1 i)
  exact ((summable_taylorSeries_neg_log hr h1).hasSum.prod_fiberwise hfib).tsum_eq.symm

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
# Character orthogonality for finite commutative groups

For a finite commutative group `G` and a domain `M` with enough roots of unity, the characters
of `G` are the monoid homomorphisms `G →* Mˣ`. This file records the *column* orthogonality
relation — the one summed over the character group — in both its punctured and its normal form,
and shows that the commutativity it assumes is necessary: the column relation fails for every
finite non-commutative group whenever the number of characters is nonzero in `M`, as it is in
characteristic zero. The underlying group-theoretic fact, that homomorphisms into a
commutative monoid separate elements only in a commutative group, is
`TauCeti.isMulCommutative_of_forall_exists_monoidHom_apply_ne_one` in
`TauCeti.GroupTheory.Commutator`.

## Main results

* `CommGroup.sum_monoidHom_apply_eq_zero_of_ne_one`: for `g ≠ 1`, the sum `∑ χ : G →* Mˣ, χ g`
  over all characters vanishes.
* `CommGroup.sum_monoidHom_apply_eq_ite`: the same sum in normal form, `Nat.card G` at `g = 1`
  and `0` elsewhere. This is the shape an indicator-formula consumer wants, and it is the `simp`
  normal form for such a sum.
* `CommGroup.sum_monoidHom_apply_eq_ite`'s tagged form,
  `CommGroup.sum_inv_mul_monoidHom_apply_eq_ite`: summing `(χ σ)⁻¹ * χ g` isolates the single
  element `σ`, giving `Nat.card G` when `g = σ` and `0` otherwise.
* `AddChar.sum_units_mul_eq_neg_one`: a nontrivial additive character of a finite field
  sums to `-1` over the nonzero elements, even after multiplication by a unit.
* `TauCeti.sum_monoidHom_apply_eq_card_of_mem_commutator`: at an element of the commutator
  subgroup the character sum is the number of characters, every summand being `1`.
* `TauCeti.exists_sum_inv_mul_monoidHom_apply_ne_ite`: **column orthogonality fails for every
  finite non-commutative group** whenever the number of characters is nonzero in `M`, as in
  characteristic zero: at the tag `1` and a nontrivial commutator the tagged sum is the number
  of characters, not `0`.

The file also registers `Fintype (G →* Mˣ)`, which Mathlib leaves at `Finite`; without it a
consumer's own character sum does not elaborate, and two ad-hoc `Fintype.ofFinite` introductions
give syntactically distinct sums. That instance needs only `LeftCancelMonoid G`, so it also serves
consumers indexing over the characters of a finite noncommutative group or monoid.

## Row orthogonality and punctured additive-character sums

The companion *row* relation — for a nontrivial `χ : G →* Mˣ`, the sum `∑ g : G, χ g` over the
group vanishes — is already `sum_hom_units_eq_zero` in
`Mathlib/RingTheory/IntegralDomain.lean`, which states exactly that for an arbitrary monoid
homomorphism `G →* R` into a domain. Specialising it to a character is
`sum_hom_units_eq_zero ((Units.coeHom M).comp χ)`, i.e. the Mathlib lemma composed with the
unit coercion and nothing else, so no declaration for it is added. Callers wanting the row
relation should use the Mathlib lemma directly. (`MulChar.sum_eq_zero_of_ne_one` in
`Mathlib/NumberTheory/MulChar/Basic.lean` is the analogous statement in the `MulChar`
vocabulary, for a multiplicative character of a finite commutative monoid valued in a domain.)

The theorem `AddChar.sum_units_mul_eq_neg_one` below is not a restatement of that full row
relation: it removes the zero term from a finite-field additive-character sum and reindexes the
remaining nonzero elements by `Fˣ`. This punctured form is what character computations over a
finite field consume directly.

The column relation genuinely is not in Mathlib in this generality. It appears there only in
specialisations: the `ZMod n` one, `DirichletCharacter.sum_characters_eq_zero` in
`Mathlib/NumberTheory/DirichletCharacter/Orthogonality.lean`, and the finite-additive-group one
over `ℂ`, `AddChar.sum_apply_eq_ite` in
`Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean` (with
`AddChar.sum_apply_eq_zero_iff_ne_zero` beside it). Neither implies the statement below, which is
multiplicative and valued in an arbitrary domain with enough roots of unity rather than in `ℂ`
or over `ZMod n`.

## References

Two of the results are adapted from
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca).

* `CommGroup.sum_monoidHom_apply_eq_zero_of_ne_one` comes from `sum_char_apply_eq_zero_of_ne_one`
  in `CebotarevDensity/ForMathlib/CharacterOrthogonality.lean`, at commit
  `8575c9df1ae0a61120ab5c964c7911414254bec7`.
* `CommGroup.sum_inv_mul_monoidHom_apply_eq_ite` comes from the private
  `sum_galoisCharacter_mul_inv_eq` in `CebotarevDensity/Cyclotomic.lean`, at commit
  `55a89985d47a3befcf6069aca1da250ff088b5c7`, where the argument is attributed to Sharifi,
  *Algebraic Number Theory*, 7.2.1 step (iii), p. 142. The source writes the sum as
  `∑ χ, χ σ * (χ τ)⁻¹` with the inverse on the second argument and concludes `σ * τ⁻¹ = 1`; the
  statement here carries the inverse on the tag and concludes `g = σ`, which is the same identity
  read in the other orientation.
-/

 section

open scoped commutatorElement

namespace AddChar

variable {F : Type*} [Field F] [Fintype F]
variable {R : Type*} [CommRing R] [IsDomain R]



end AddChar

variable {G : Type*} [Finite G] {M : Type*} [CommRing M] [IsDomain M]



namespace CommGroup

variable [CommGroup G] [HasEnoughRootsOfUnity M (Monoid.exponent G)]

/-- **Character-column orthogonality** for a finite commutative group `G` valued in a domain `M`
with enough roots of unity: for `g ≠ 1`, the sum of `χ g` over all characters `χ : G →* Mˣ`
vanishes. -/
theorem sum_monoidHom_apply_eq_zero_of_ne_one {g : G} (hg : g ≠ 1) :
    ∑ χ : G →* Mˣ, (χ g : M) = 0 := by
  -- A specialisation of `sum_hom_units_eq_zero` on the dual group `G →* Mˣ` along the
  -- evaluation homomorphism `χ ↦ χ g`.
  obtain ⟨χ₀, hχ₀⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity G M hg
  exact sum_hom_units_eq_zero ((Units.coeHom M).comp (MonoidHom.eval g))
    fun h ↦ hχ₀ <| Units.val_eq_one.mp <| DFunLike.congr_fun h χ₀

/-- **Column orthogonality in normal form**: the character sum is `Nat.card G` at the identity
and vanishes elsewhere. This covers both cases at once, and states the identity value as the
cardinality of `G` itself rather than of its dual, which is the shape an indicator-formula
consumer wants. -/
@[simp]
theorem sum_monoidHom_apply_eq_ite [DecidableEq G] (g : G) :
    ∑ χ : G →* Mˣ, (χ g : M) = if g = 1 then (Nat.card G : M) else 0 := by
  split
  · next hg =>
    subst hg
    -- the dual of `G` has the cardinality of `G`, by Mathlib's character duality
    have hcard : Fintype.card (G →* Mˣ) = Nat.card G := by
      simpa using card_monoidHom_of_hasEnoughRootsOfUnity G M
    simp [hcard]
  · next hg => exact sum_monoidHom_apply_eq_zero_of_ne_one hg

/-- **Tagged column orthogonality.** Summing `(χ σ)⁻¹ * χ g` over all characters isolates the
single element `σ`: the sum is `Nat.card G` when `g = σ` and `0` otherwise. This is the form a
fibre-selecting argument uses, `sum_monoidHom_apply_eq_ite` being the case `σ = 1`.

The inverse sits on the tag `σ`, not on the argument `g`. Without it the sum is
`∑ χ, χ (σ * g)`, which is the indicator of `g = σ⁻¹` — a different fibre, and one that genuinely
differs whenever `σ` is not an involution. -/
@[simp]
theorem sum_inv_mul_monoidHom_apply_eq_ite [DecidableEq G] (σ g : G) :
    ∑ χ : G →* Mˣ, (((χ σ)⁻¹ : Mˣ) : M) * ((χ g : Mˣ) : M) =
      if g = σ then (Nat.card G : M) else 0 := by
  have key : ∀ χ : G →* Mˣ, (((χ σ)⁻¹ : Mˣ) : M) * ((χ g : Mˣ) : M) = ((χ (σ⁻¹ * g) : Mˣ) : M) :=
    fun χ ↦ by rw [map_mul, map_inv, Units.val_mul]
  simp only [key, sum_monoidHom_apply_eq_ite, inv_mul_eq_one, eq_comm]

end CommGroup

namespace TauCeti

variable [Group G]





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
# Completely multiplicative ideal weights

The completely multiplicative specializations of `TauCeti.IdealArithmeticFunction`: the two
carriers on which every Euler product, Hecke character and character-family argument of this
development is stated.

A `TauCeti.MultiplicativeIdealWeight K` is a monoid-with-zero homomorphism
`Ideal (𝓞 K) →*₀ ℂ` killing only finitely many height-one primes, and
`TauCeti.UnitaryIdealWeight K` is the subtype of those whose values have modulus `1` away from
that finite bad set. Using Mathlib's `→*₀` vocabulary is what pins the zero-ideal law
`χ ⊥ = 0`; the finiteness condition is what bounds the bad local factors of the Euler product.

Both carriers are *degree one*: the value at `𝔭 ^ n` is forced to be `χ 𝔭 ^ n`. They are
therefore deliberately too narrow for the ideal Möbius function or for coefficient systems
whose prime-power values are independent local data; those get separate carriers.

The organising notion is `Ideal.IsPrimeTo`, an ideal of a Dedekind domain being nonzero and
divisible by no prime of a given set; it is stated for a general Dedekind domain because
nothing in it is specific to a number field. The good ideals of a weight are the ideals
prime to its bad primes, and `Ideal.IsPrimeTo.induction_on` factors such an ideal into
good primes; this is the engine behind both
`TauCeti.MultiplicativeIdealWeight.apply_ne_zero_iff_isGood` and
`TauCeti.UnitaryIdealWeight.norm_eq_one`.

## Main declarations

* `Ideal.IsPrimeTo`: an ideal is nonzero and no prime of `S` divides it, with its
  multiplicativity (`Ideal.isPrimeTo_mul_iff`) and its induction principle
  (`Ideal.IsPrimeTo.induction_on`);
* `TauCeti.MultiplicativeIdealWeight`: the general completely multiplicative carrier, its
  `TauCeti.MultiplicativeIdealWeight.badPrimes` and its good ideals
  (`TauCeti.MultiplicativeIdealWeight.IsGood`);
* `TauCeti.MultiplicativeIdealWeight.apply_ne_zero_iff_isGood`: a weight is nonzero exactly on
  the good ideals;
* `TauCeti.MultiplicativeIdealWeight.ext_heightOneSpectrum`: a weight is determined by its
  values at the height-one primes;
* `TauCeti.MultiplicativeIdealWeight.ofBadPrimes`, the pointwise `CommMonoid` structure (whose
  unit is the trivial weight), `TauCeti.MultiplicativeIdealWeight.restrict`,
  `TauCeti.MultiplicativeIdealWeight.conj` and
  `TauCeti.MultiplicativeIdealWeight.normTwist`: the constructors and operations;
* `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood` and
  `TauCeti.MultiplicativeIdealWeight.IsTrivialOnGood`: the weights agreeing with a purely
  imaginary norm twist, respectively with the trivial weight, on their good ideals, with the
  structure theorem `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood.eq_normTwist`, its
  converse `TauCeti.MultiplicativeIdealWeight.isNormTwistOnGood_normTwist_ofBadPrimes`, and the
  behaviour of the parameter under conjugation, the pointwise product and a further twist;
* `TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction`: passage to the general
  carrier, inverted by `TauCeti.IdealArithmeticFunction.zeroExtend`;
* `TauCeti.UnitaryIdealWeight`: the unitary subtype, with
  `TauCeti.UnitaryIdealWeight.norm_eq_one` on all good ideals,
  `TauCeti.UnitaryIdealWeight.norm_normTwist` for the modulus of an arbitrary norm twist,
  `TauCeti.UnitaryIdealWeight.ofPowEqOne` for finite-order weights, and the operations
  `TauCeti.UnitaryIdealWeight.conj`, `TauCeti.UnitaryIdealWeight.restrict` and
  `TauCeti.UnitaryIdealWeight.normTwist` (the last for the imaginary norm twists only), and
  `TauCeti.UnitaryIdealWeight.toIdealArithmeticFunction` for its passage to the general carrier;
* `TauCeti.MultiplicativeIdealWeight.map` and `TauCeti.UnitaryIdealWeight.map`, with their
  equivalences `mapEquiv`: functoriality under an isomorphism `K ≃+* L` of the ambient fields,
  together with the identity and composition laws, the preservation of the pointwise product
  (`map_one` and `map_mul` on both carriers), the naturality of restriction, conjugation and norm
  twists, and the compatibilities
  `TauCeti.MultiplicativeIdealWeight.badPrimes_map` and
  `TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_map`.

## Rejection tests

The two worked negative examples of this layer are proved here.
`TauCeti.MultiplicativeIdealWeight.coe_ne_const_one` says the everywhere-one function on *all*
integral ideals underlies no weight, because `→*₀` forces the value `0` at `⊥` — the
everywhere-one function on the *nonzero* ideals is the trivial weight instead
(`TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_one`).
`TauCeti.UnitaryIdealWeight.norm_normTwist_apply_ne_one` says that a norm twist with
`Re z ≠ 0` changes the modulus at every good ideal of absolute norm greater than one, so such
twists live only in the general carrier.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* `TauCetiRoadmap/ArithmeticDirichletSeries/README.md` and its `Suggested.lean` target
  signatures: this file implements the Layer 0 export contract stated there, and follows its
  naming and organization for the two weight carriers.
-/

 section

namespace TauCeti

open _root_.NumberField _root_.IsDedekindDomain _root_.nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]



/-!
### The general carrier of completely multiplicative ideal weights
-/



namespace MultiplicativeIdealWeight





@[simp]
theorem coe_toMonoidWithZeroHom (χ : MultiplicativeIdealWeight K) :
    ⇑χ.toMonoidWithZeroHom = ⇑χ := rfl







/-- A multiplicative ideal weight is determined by its values at the height-one primes: every
nonzero ideal of `𝓞 K` is a product of them. -/
theorem ext_heightOneSpectrum {χ ψ : MultiplicativeIdealWeight K}
    (h : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), χ 𝔭.asIdeal = ψ 𝔭.asIdeal) : χ = ψ := by
  ext I
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => rw [map_zero, map_zero]
  | h₂ x hx => rw [Ideal.isUnit_iff.mp hx, apply_top, apply_top]
  | h₃ a p _ hp ih =>
    rw [_root_.map_mul, _root_.map_mul, ih, h ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩]







variable {χ : MultiplicativeIdealWeight K}





theorem apply_eq_zero_iff_not_isGood (χ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) :
    χ I = 0 ↔ ¬ χ.IsGood I := by
  rw [← not_ne_iff, χ.apply_ne_zero_iff_isGood]

/-!
### Constructors and operations
-/

section Operations

variable {S : Set (HeightOneSpectrum (𝓞 K))}





































/-- Restricting the trivial weight away from `S` gives the indicator weight of ideals prime to
every prime in `S`. -/
@[simp]
theorem one_restrict (hS : S.Finite) :
    (1 : MultiplicativeIdealWeight K).restrict S hS = ofBadPrimes S hS :=
  one_mul _



















/-!
### Weights that are norm twists on their good locus
-/

























end Operations

/-!
### Passage to the general carrier, and the zero-ideal rejection test
-/













@[simp]
theorem toIdealArithmeticFunction_one :
    (1 : MultiplicativeIdealWeight K).toIdealArithmeticFunction = 1 := by
  ext I
  have hI : (I : Ideal (𝓞 K)) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  simp [one_apply, hI]





/-!
### Functoriality under an isomorphism of fields
-/

section Transport

variable {L M : Type*} [Field L] [NumberField L] [Field M] [NumberField M]





















/-! Transport preserves the pointwise `CommMonoid` structure. -/













end Transport

end MultiplicativeIdealWeight

/-!
### The unitary subtype
-/



namespace UnitaryIdealWeight

/-- **A unitary weight has modulus one on every good ideal**, extending its defining condition
from good primes to the entire good-ideal locus. -/
theorem norm_eq_one (χ : UnitaryIdealWeight K) {I : Ideal (𝓞 K)} (hI : χ.1.IsGood I) :
    ‖χ.1 I‖ = 1 := by
  refine hI.induction_on (by simp) fun 𝔭 J h𝔭 _ ih ↦ ?_
  rw [map_mul, norm_mul, χ.2 𝔭 h𝔭, ih, one_mul]

-- Source. The statement and its proof follow `DirichletCharacter.norm_le_one` in Mathlib's
-- `Mathlib/NumberTheory/DirichletCharacter/Bounds.lean`, transposed from a Dirichlet character on
-- `ZMod n` to a unitary ideal weight: the case split there is on `IsUnit a` and closes with
-- `map_nonunit`, here it is on `MultiplicativeIdealWeight.IsGood` and closes with
-- `apply_eq_zero_iff_not_isGood`.

/-- **A unitary weight is bounded by one on every ideal.** The bound is unconditional: it carries
no goodness hypothesis, so a comparison indexed by all of `(Ideal (𝓞 K))⁰` can apply it termwise.
`norm_eq_one` is sharper where it applies, but obliges the caller to split that index type first;
this is the form a convergence estimate wants. -/
theorem norm_le_one (χ : UnitaryIdealWeight K) (I : Ideal (𝓞 K)) : ‖χ.1 I‖ ≤ 1 := by
  by_cases hI : χ.1.IsGood I
  · exact (norm_eq_one χ hI).le
  · rw [(MultiplicativeIdealWeight.apply_eq_zero_iff_not_isGood χ.1 I).mpr hI, norm_zero]
    exact zero_le_one















@[simp]
theorem val_ofPowEqOne (χ : MultiplicativeIdealWeight K) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∉ χ.badPrimes → χ 𝔭.asIdeal ^ n = 1) :
    (ofPowEqOne χ hn h).1 = χ := (rfl)



















@[simp]
theorem val_restrict (χ : UnitaryIdealWeight K) (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) : (restrict χ S hS).1 = χ.1.restrict S hS := (rfl)



section Transport

variable {L M : Type*} [Field L] [NumberField L] [Field M] [NumberField M]















/-! Transport preserves the pointwise `CommMonoid` structure of the unitary carrier too. -/











end Transport



@[simp]
theorem toIdealArithmeticFunction_apply (χ : UnitaryIdealWeight K) (I : (Ideal (𝓞 K))⁰) :
    χ.toIdealArithmeticFunction I = χ.1 I := (rfl)

/-- The ideal arithmetic function of a unitary weight agrees with that of its underlying
multiplicative weight. -/
theorem toIdealArithmeticFunction_eq_val (χ : UnitaryIdealWeight K) :
    χ.toIdealArithmeticFunction = χ.1.toIdealArithmeticFunction := by
  funext I
  rw [toIdealArithmeticFunction_apply,
    MultiplicativeIdealWeight.toIdealArithmeticFunction_apply]











end UnitaryIdealWeight

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
# Finite real-cutoff carriers for Northcott functions

This file packages the finite carrier selected by a real cutoff for a natural-valued Northcott
function, together with generic summatory functions over that carrier. The carrier depends only
on the integer part of the cutoff, and for a nonnegative cutoff it agrees with the one selected by
its natural floor.
-/

 section

namespace TauCeti

open Filter
open scoped Topology

variable {ι : Type*} (N : ι → ℕ) [Northcott N]





/-- An index belongs to `normLE N x` exactly when its `N`-value is at most the inclusive
real cutoff `x`. -/
@[simp, grind =]
theorem mem_normLE {i : ι} {x : ℝ} : i ∈ normLE N x ↔ (N i : ℝ) ≤ x := by
  simp [normLE]

@[simp]
theorem coe_normLE (x : ℝ) : (normLE N x : Set ι) = {i : ι | (N i : ℝ) ≤ x} := by
  ext i
  simp















/-! ### Generic summatory functions -/



/-- Evaluating `summatory N w` at `x` gives the finite sum of `w` over `normLE N x`. -/
theorem summatory_apply {M : Type*} [AddCommMonoid M] (w : ι → M) (x : ℝ) :
    summatory N w x = ∑ i ∈ normLE N x, w i := by
  rw [summatory]





























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







/-! ### The prime base and the exponent of a prime-power ideal -/



























































variable (K)

/-! ### Summatory functions over ideals and over primes -/









/-- An ideal summatory function is the sum of its weight over the inclusive cutoff carrier. -/
theorem idealSummatory_apply {M : Type*} [AddCommMonoid M] (w : (Ideal (𝓞 K))⁰ → M) (x : ℝ) :
    idealSummatory K w x = ∑ I ∈ idealsLE K x, w I :=
  summatory_apply _ w x























variable {K}

namespace MultiplicativeIdealWeight

variable (χ : MultiplicativeIdealWeight K)



end MultiplicativeIdealWeight

variable (K)





/-- **An ideal summatory function is a partial sum of norm coefficients.** The inclusive sum of
`f` over the nonzero integral ideals of absolute norm at most `x` is `∑_{n=1}^{⌊x⌋₊}` of the norm
coefficients of `f`, in the `Finset.Icc 1` form of Mathlib's `LSeries_eq_mul_integral`. -/
theorem idealSummatory_eq_sum_Icc_normCoeff (f : IdealArithmeticFunction K) (x : ℝ) :
    idealSummatory K f x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, normCoeff K f n := by
  rw [idealSummatory_eq_sum_range_normFiber, Nat.range_succ_eq_Icc_zero,
    ← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le _), Finset.sum_insert (by simp),
    normFiber_zero, Finset.sum_empty, zero_add, zero_add]
  exact Finset.sum_congr rfl fun n _ ↦ (normCoeff_eq_sum_normFiber K f n).symm



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
# The trivial ideal weight and Dedekind zeta coefficients

This file identifies the norm coefficients of the trivial ideal weight with the coefficients of
the Dedekind zeta function.  There is one necessary exception: Mathlib's coefficient counts all
integral ideals and therefore has value `1` at index zero, contributed by the zero ideal, whereas
an `ArithmeticFunction` has value zero there.  Since `LSeries` ignores its zero coefficient, the
two coefficient systems define the same series.

For the rational field the ring of integers is isomorphic to `ℤ`.  Mapping an ideal through this
isomorphism and using `Int.ideal_span_absNorm_eq_self` shows that there is exactly one ideal of
each positive norm.  Thus the trivial ideal weight over `ℚ` regroups to the constant coefficient
`1` at every positive index, as for the Riemann zeta function.

## Roadmap role

This is Layer **1.3**, the trivial specialization, of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  It completes Layer 1 without asserting the
exact abscissa of convergence; that is Layer 5, proved in
`TauCeti.abscissaOfAbsConv_normCoeff_one`.
-/

 section

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.NumberField

variable (K : Type*) [Field K] [NumberField K]





/-- The Dedekind zeta function is the `LSeries` of `dedekindZetaCoeff`. -/
theorem dedekindZeta_eq_LSeries_dedekindZetaCoeff (s : ℂ) :
    NumberField.dedekindZeta K s = LSeries (fun n ↦ (dedekindZetaCoeff K n : ℂ)) s := by
  simp [NumberField.dedekindZeta, dedekindZetaCoeff]

private def normFiberSubtypeEquiv {n : ℕ} (hn : n ≠ 0) :
    {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) = n} ≃
      {I : Ideal (𝓞 K) // Ideal.absNorm I = n} where
  toFun I := ⟨I.1, I.2⟩
  invFun I :=
    ⟨⟨I.1, by
      rw [← Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors]
      exact fun hzero ↦ hn (I.2.symm.trans hzero)⟩, I.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Away from zero, the cardinality of the finite nonzero-ideal norm fibre is the corresponding
Dedekind zeta coefficient. -/
theorem card_normFiber_eq_dedekindZetaCoeff {n : ℕ} (hn : n ≠ 0) :
    (normFiber K n).card = dedekindZetaCoeff K n := by
  rw [← Nat.card_eq_finsetCard, dedekindZetaCoeff]
  exact Nat.card_congr <|
    (Equiv.subtypeEquivRight fun I ↦ mem_normFiber (K := K)).trans
      (normFiberSubtypeEquiv K hn)

/-- The trivial ideal arithmetic function regroups to the Dedekind zeta coefficients away from
zero.  At zero its norm coefficient is forced to vanish by the `ArithmeticFunction` carrier. -/
@[simp]
theorem normCoeff_one_apply (n : ℕ) :
    normCoeff K (1 : IdealArithmeticFunction K) n =
      if n = 0 then 0 else dedekindZetaCoeff K n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, normCoeff_eq_sum_normFiber]
    simp [card_normFiber_eq_dedekindZetaCoeff K hn]



/-- Regrouping the trivial ideal weight gives Mathlib's Dedekind zeta function. -/
theorem dedekindZeta_eq_LSeries_normCoeff_one (s : ℂ) :
    NumberField.dedekindZeta K s = LSeries (normCoeff K (1 : IdealArithmeticFunction K)) s := by
  rw [dedekindZeta_eq_LSeries_dedekindZetaCoeff]
  apply LSeries_congr
  intro n hn
  rw [normCoeff_one_apply, if_neg hn]













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

/-- The trivial ideal weight has norm coefficient the number of nonzero integral ideals of the
given absolute norm, so its absolute value is that count. -/
theorem norm_normCoeff_one (n : ℕ) :
    ‖normCoeff K (1 : IdealArithmeticFunction K) n‖ = (normFiber K n).card := by
  rw [normCoeff_eq_sum_normFiber]
  simp

/-- The norm coefficients of a unitary weight are bounded in modulus by those of the trivial
weight, which count the ideals of each norm. -/
theorem UnitaryIdealWeight.norm_normCoeff_le_norm_normCoeff_one (χ : UnitaryIdealWeight K) (n : ℕ) :
    ‖normCoeff K χ.toIdealArithmeticFunction n‖ ≤
      ‖normCoeff K (1 : IdealArithmeticFunction K) n‖ := by
  rw [norm_normCoeff_one, normCoeff_eq_sum_normFiber]
  refine (norm_sum_le _ _).trans ?_
  simpa using Finset.sum_le_sum fun I (_ : I ∈ normFiber K n) ↦ χ.norm_le_one (I : Ideal (𝓞 K))



/-! ### The exact abscissa of the trivial ideal weight -/

/-- The upper linear ideal count makes the partial sums of the trivial norm coefficients `O(n)`. -/
theorem isBigO_sum_norm_normCoeff_one :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ‖normCoeff K (1 : IdealArithmeticFunction K) k‖)
      =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
  obtain ⟨b⟩ := idealCount_linearBounds K
  refine Asymptotics.IsBigO.of_bound b.upper ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [sum_norm_normCoeff_one, Real.rpow_one, Real.norm_natCast, Real.norm_natCast]
  exact b.card_le n h1













/-! ### The exact abscissa, and its Dedekind zeta form -/





/-- The ideal-indexed Dirichlet series of the trivial ideal weight converges absolutely exactly on
`Re s > 1`. -/
theorem summable_idealTerm_one_iff {K : Type*} [Field K] [NumberField K] {s : ℂ} :
    Summable (idealTerm K (1 : IdealArithmeticFunction K) s) ↔ 1 < s.re := by
  refine ⟨fun h ↦ (LSeriesSummable_normCoeff_one_iff K).mp (LSeriesSummable_normCoeff K h),
    fun h ↦ ?_⟩
  exact summable_idealTerm_of_nonneg K 1 (fun _ ↦ zero_le_one)
    ((LSeriesSummable_normCoeff_one_iff K).mpr h)

/-- **A uniformly bounded weight converges wherever the trivial weight does.** If every value of
`f` on a nonzero integral ideal has modulus at most `C`, its ideal-indexed Dirichlet series
converges absolutely on `Re s > 1`.

The bound may be any nonnegative real — a negative `C` makes the hypothesis unsatisfiable, since
`‖f I‖` is a norm — and no `C = 1` normalisation is wanted, since a weight is often bounded by
something other than `1` without being rescaled. The unitary case — a Dirichlet or Galois
character, of modulus `1` at the good primes and `0` at the bad ones — is `C = 1`, and is packaged
as `summable_idealTerm_of_unitary_of_one_lt_re`. Stating the hypothesis here as a bound rather than
as unitarity is what lets the vanishing at the bad primes pass without a special case.

Only one direction holds, unlike `summable_idealTerm_one_iff`: a weight that vanishes identically
is bounded by every nonnegative `C` and converges everywhere. -/
theorem summable_idealTerm_of_bounded_of_one_lt_re {K : Type*} [Field K] [NumberField K]
    {f : IdealArithmeticFunction K} {C : ℝ} (hf : ∀ I : (Ideal (𝓞 K))⁰, ‖f I‖ ≤ C) {s : ℂ}
    (hs : 1 < s.re) : Summable (idealTerm K f s) := by
  refine Summable.of_norm_bounded
    (g := fun I ↦ C * ‖idealTerm K (1 : IdealArithmeticFunction K) s I‖)
    (((summable_idealTerm_one_iff.mpr hs).norm).mul_left C) fun I ↦ ?_
  rw [norm_idealTerm, norm_idealTerm]
  have hpos : (0 : ℝ) < (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s.re :=
    Real.rpow_pos_of_pos (by exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I) _
  have hone : ‖(1 : IdealArithmeticFunction K) I‖ = 1 := by simp
  rw [hone, mul_one_div]
  gcongr
  exact hf I

/-- **A unitary weight converges on `Re s > 1`.** The specialization of
`summable_idealTerm_of_bounded_of_one_lt_re` at `C = 1`, through
`TauCeti.UnitaryIdealWeight.norm_le_one`: a unitary weight has modulus `1` on the good ideals and
vanishes on the rest, so it is bounded by `1` on all of them and the caller is left no case split.

This is the form the Euler-product code consumes, its `hasProd_eulerFactor` asking for exactly a
`Summable (idealTerm K · s)` hypothesis on the weight's passage to `IdealArithmeticFunction`. -/
theorem summable_idealTerm_of_unitary_of_one_lt_re {K : Type*} [Field K] [NumberField K]
    (χ : UnitaryIdealWeight K) {s : ℂ} (hs : 1 < s.re) :
    Summable (idealTerm K χ.toIdealArithmeticFunction s) := by
  refine summable_idealTerm_of_bounded_of_one_lt_re (C := 1) (fun I ↦ ?_) hs
  rw [UnitaryIdealWeight.toIdealArithmeticFunction_apply]
  exact χ.norm_le_one _







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
# Canonical local factors and formal Euler products for ideal arithmetic functions

This file develops the Euler-product layer for arithmetic functions on nonzero ideals. It builds
the canonical formal power series at each height-one prime and sends that series into Mathlib's
`ArithmeticFunction.ofPowerSeries` API. The resulting local arithmetic factor has the prescribed
prime-power values and vanishes away from powers of the prime-ideal norm.

It then restricts an ideal arithmetic function to the nonzero ideals whose prime factors lie in a
prescribed set of height-one primes, and proves that for a *finite* set of primes the norm
coefficients of that restriction are exactly the product of the local factors, taken in Mathlib's
Dirichlet convolution of arithmetic functions. Passing to Mathlib's formal Euler product gives the
norm coefficients of the original function. Everything here is a formal identity of coefficients:
no analytic convergence hypothesis enters.

## Main definitions

* `TauCeti.IdealArithmeticFunction.localPowerSeries` has coefficient `f (P ^ n)` at `n`.
* `TauCeti.IdealArithmeticFunction.localArithmeticFactor` realizes that power series as an
  arithmetic function supported on powers of `N(P)`.
* `TauCeti.IdealArithmeticFunction.supportedPart f S` is `f` restricted to the nonzero ideals all
  of whose prime factors lie in `S`, and zero elsewhere.

## Main results

* `TauCeti.IdealArithmeticFunction.supportedPart_insert`: for a multiplicative `f`, adjoining one
  prime to the support convolves the restriction with the restriction to the powers of that prime.
* `TauCeti.IdealArithmeticFunction.normCoeff_supportedPart`: the **finite Euler product**
  `normCoeff (supportedPart f S) = ∏ P ∈ S, localArithmeticFactor f P` for a multiplicative `f`
  and a finite set `S` of height-one primes.
* `TauCeti.IdealArithmeticFunction.normCoeff_eq_eulerProduct`: the norm coefficients of a
  multiplicative ideal arithmetic function are Mathlib's formal Euler product of its canonical
  local factors.

## Implementation notes

"Supported on `S`" is spelled `Ideal.IsPrimeTo · Sᶜ`: no prime *outside* `S` divides the ideal.
That predicate, and the splitting `Ideal.IsPrimeTo.exists_eq_pow_mul` of an ideal into a prime
power times a cofactor together with its uniqueness `Ideal.eq_and_eq_of_pow_mul_eq_pow_mul`, live
in `TauCeti/RingTheory/DedekindDomain/Ideal.lean`, since nothing in them is specific to a number
field. Uniqueness is what makes the induction work: it is why exactly one summand of the ideal
convolution survives at each ideal. The multiplicativity of `f` over a prime-power factorization,
`TauCeti.IdealArithmeticFunction.IsMultiplicative.map_prod_pow`, likewise lives with the predicate
it elaborates, in `TauCeti/NumberTheory/ArithmeticDirichletSeries/Basic.lean`.

`TauCeti.MultiplicativeIdealWeight.restrict` is the opposite regime and is not a substitute:
it restricts *away from* a **finite** set of primes and stays inside the bundled weight carrier. A
finite Euler product needs support on a *finite* set of primes, so all but finitely many primes are
bad; such a function is never a `MultiplicativeIdealWeight`, whose zero support is finite by
definition. Hence `supportedPart` is a plain ideal arithmetic function.

Finiteness is what carries the finite products to the full Euler product. A nonzero ideal has
only finitely many prime divisors, and only finitely many primes have norm at most a given `n`, so
at a fixed norm coefficient the restriction `supportedPart f S` already agrees with `f` as soon as
`S` contains those primes. Each finite product is therefore eventually the exact norm coefficient,
and Mathlib's `ArithmeticFunction.eulerProduct`, being the limit of those finite products, computes
the norm coefficients of `f` itself. The local factors are derived from `f` rather than stored, so
this identity holds for any multiplicative `f` with no further data.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `ArithmeticFunction.ofPowerSeries` and `ArithmeticFunction.eulerProduct` APIs.
* `TauCetiRoadmap/ArithmeticDirichletSeries/Suggested.lean`, whose local-factor target signatures
  and naming are adapted here.
-/

 section

open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K]



/-- A prime power, as a nonzero integral ideal, has the expected underlying ideal. -/
@[simp]
theorem coe_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    (primeIdealPow P e : Ideal (𝓞 K)) = P.asIdeal ^ e :=
  (rfl)

variable [NumberField K]

/-- The absolute norm is multiplicative on prime powers. -/
theorem absNorm_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    Ideal.absNorm (primeIdealPow P e : Ideal (𝓞 K)) = Ideal.absNorm P.asIdeal ^ e := by
  rw [coe_primeIdealPow, map_pow]

omit [NumberField K] in
/-- Distinct primes give distinct first powers, so a family indexed by the primes is a subfamily
of one indexed by the nonzero ideals. -/
theorem primeIdealPow_one_injective :
    Function.Injective fun P : HeightOneSpectrum (𝓞 K) ↦ primeIdealPow P 1 := fun P Q h ↦
  HeightOneSpectrum.asIdeal_injective
    (by simpa only [coe_primeIdealPow, pow_one] using
      congrArg (Subtype.val : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K)) h)

/-- Distinct exponents give distinct prime powers. -/
theorem primeIdealPow_injective (P : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (primeIdealPow P) := fun m n h ↦
  Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm P)
    (by simpa only [absNorm_primeIdealPow] using
      congrArg (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) h)

end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti



namespace IdealArithmeticFunction

variable {K : Type*} [Field K]

variable [NumberField K]



























/-! ### Finite Euler products -/



variable {f : IdealArithmeticFunction K} {S : Set (HeightOneSpectrum (𝓞 K))}
  {A : (Ideal (𝓞 K))⁰}































end IdealArithmeticFunction

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
# Euler-product coefficient data over a number field

This file bundles the algebraic input for an Euler product over the height-one primes of the ring
of integers of a number field. An `EulerProductData K` consists of an ideal arithmetic function
that is multiplicative on relatively prime nonzero ideals. The prime-power series and local
arithmetic factors are canonically derived from the function as defined in
`EulerProduct/Basic.lean`, so nothing about the local behaviour is stored: the bundle carries
exactly the one algebraic hypothesis that an Euler product consumes.

The formal Euler-product identity follows from
`IdealArithmeticFunction.normCoeff_eq_eulerProduct`: coprime multiplicativity and unique
factorization prove that `normCoeff` is Mathlib's `ArithmeticFunction.eulerProduct` of the
canonical local factors.

Two hypotheses of the classical theory are deliberately absent, because the identity proved here
does not need either. There is no distinguished finite set of exceptional primes: multiplicativity
is required on every coprime pair of nonzero ideals, and the local factor at a prime is read off
from the coefficients at its powers, good or bad. There is also no analytic input: the identity is
an equality of arithmetic functions, and the convergence of the evaluated factors to an infinite
product is a separate question.

## Main definitions

* `TauCeti.EulerProductData` bundles a multiplicative ideal coefficient system.
* `TauCeti.EulerProductData.ofMultiplicativeIdealWeight` regards a degree-one ideal weight as
  Euler-product data.
* Pointwise multiplication, complex conjugation, and restriction away from sets of primes
  preserve the bundle.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `ArithmeticFunction.ofPowerSeries` and `ArithmeticFunction.eulerProduct` APIs.
-/

 section

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)



namespace EulerProductData

variable {K : Type*} [Field K] [NumberField K]



























/-- The coefficient function underlying the Euler-product data of a multiplicative ideal weight. -/
@[simp]
theorem toIdealArithmeticFunction_ofMultiplicativeIdealWeight (χ : MultiplicativeIdealWeight K) :
    (ofMultiplicativeIdealWeight χ).toIdealArithmeticFunction = χ.toIdealArithmeticFunction := by
  funext I
  rfl





















end EulerProductData

end TauCeti

end
end

section
set_option autoImplicit true
namespace TauCeti.IdealArithmeticFunction
end TauCeti.IdealArithmeticFunction
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The analytic Euler product of an ideal arithmetic function

`TauCeti.EulerProductData.normCoeff_eq_eulerProduct` identifies the norm coefficients of bundled
Euler-product data with a formal Euler product, coefficient by coefficient. This file supplies the
analytic statement it does not: where the Dirichlet series indexed by the nonzero ideals converges
absolutely, the infinite product of the local Euler factors converges, in the unrestricted sense
of `HasProd` over the height-one primes, to the `LSeries` of the norm coefficients.

The local factor at a height-one prime `P` is the `LSeries` of the canonical local arithmetic
factor, equivalently the prime-power Dirichlet series `∑' e, f (P ^ e) / N(P ^ e) ^ s`. For a
completely multiplicative weight that series is geometric, and the factor takes the familiar
closed form `(1 - χ(P) N(P) ^ (-s))⁻¹`; specializing to the trivial weight gives the Euler
product of the Dedekind zeta function.

## Main definitions

* `TauCeti.EulerProductData.eulerFactor`: the local Euler factor at a height-one prime.

## Main results

* `TauCeti.EulerProductData.hasProd_eulerFactor`: the **analytic Euler product**, when the
  ideal-indexed Dirichlet series converges absolutely at `s`.
* `TauCeti.EulerProductData.norm_absNorm_cpow_neg_le_radius_localPowerSeries`: a lower bound for
  the convergence radius of a local power series from absolute convergence at a real point.
* `TauCeti.MultiplicativeIdealWeight.hasProd_eulerFactor`: the same product, with the local factors
  in the closed geometric form available for a completely multiplicative weight.
* `TauCeti.MultiplicativeIdealWeight.LSeries_ne_zero_of_summable_idealTerm`: the `L`-series is
  **nonzero** wherever the ideal-indexed series converges absolutely.
* `TauCeti.dedekindZeta_eulerProduct_hasProd`: the **Euler product of the Dedekind zeta
  function**, valid on `Re s > 1`.
* `TauCeti.dedekindZeta_ne_zero_of_one_lt_re`: the Dedekind zeta function is **nonzero** on
  `Re s > 1`.
* `IsDedekindDomain.HeightOneSpectrum.one_lt_norm_absNorm_cpow` and
  `IsDedekindDomain.HeightOneSpectrum.absNorm_cpow_sub_one_ne_zero`: analytic bounds for the
  complex powers of prime-ideal norms on the right half-plane.
* `IsDedekindDomain.HeightOneSpectrum.logDeriv_one_sub_absNorm_cpow_neg`: the logarithmic
  derivative of a deleted Euler factor.

The nonvanishing is pointwise, at each `s` where the ideal-indexed series converges absolutely, and
nothing is claimed off that region. It is not a formality: an unconditionally convergent product of
nonzero factors may still vanish.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `EulerProduct` API, whose `Nat.Primes`-indexed statements this file mirrors for the
  height-one primes of a number field.
-/

 section

open scoped _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute norm of a height-one prime, cast to `ℂ`, is nonzero. -/
theorem natCast_absNorm_ne_zero (P : HeightOneSpectrum (𝓞 K)) :
    (Ideal.absNorm P.asIdeal : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (NumberField.HeightOneSpectrum.one_lt_absNorm P).ne_bot

/-- On `Re s > 0`, `N(𝔭) ^ s` lies outside the closed unit disc. -/
theorem one_lt_norm_absNorm_cpow (P : HeightOneSpectrum (𝓞 K)) {s : ℂ}
    (hs : 0 < s.re) : 1 < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ s‖ := by
  have hP := NumberField.HeightOneSpectrum.one_lt_absNorm P
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  exact Real.one_lt_rpow (by exact_mod_cast hP) hs







end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.ComplexOrder

variable {K : Type*} [Field K] [NumberField K]

namespace EulerProductData

open _root_.TauCeti.IdealArithmeticFunction

variable (D : EulerProductData K) {s : ℂ}

/-! ### The local Euler factor -/







end EulerProductData

namespace IdealArithmeticFunction

variable {f : IdealArithmeticFunction K} {s : ℂ}

/-! ### Restriction to a set of primes, analytically -/













/-- **The prime terms are a subseries of the ideal terms.** Each height-one prime contributes its
own ideal as the `e = 1` member of its power series, and distinct primes give distinct ideals, so
absolute convergence over ideals restricts to the primes. Multiplicativity plays no part. -/
theorem summable_idealTerm_primeIdealPow_one (hs : Summable (idealTerm K f s)) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦ idealTerm K f s (P.primeIdealPow 1) :=
  hs.comp_injective HeightOneSpectrum.primeIdealPow_one_injective

end IdealArithmeticFunction

namespace EulerProductData

open _root_.TauCeti.IdealArithmeticFunction

variable (D : EulerProductData K) {s : ℂ}













/-! ### The infinite Euler product -/







end EulerProductData

/-! ### Completely multiplicative weights -/

namespace MultiplicativeIdealWeight

open _root_.TauCeti.IdealArithmeticFunction

variable (χ : MultiplicativeIdealWeight K) {s : ℂ}

/-- The ideal terms of a completely multiplicative weight along the powers of a prime form a
geometric progression. -/
@[simp]
theorem idealTerm_toIdealArithmeticFunction_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ)
    (s : ℂ) :
    idealTerm K χ.toIdealArithmeticFunction s (P.primeIdealPow e) =
      (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) ^ e := by
  rw [idealTerm_def, toIdealArithmeticFunction_apply,
    P.absNorm_primeIdealPow, P.coe_primeIdealPow,
    map_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
    Complex.cpow_nat_mul, div_pow]

/-- **The local ratio of a convergent weight is a contraction.** Absolute convergence of the
ideal-indexed Dirichlet series forces the geometric ratio at each prime to have modulus less than
one, because the powers of that prime already contribute a geometric subseries. -/
theorem norm_div_lt_one_of_summable_idealTerm
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s))
    (P : HeightOneSpectrum (𝓞 K)) :
    ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖ < 1 := by
  rw [← summable_geometric_iff_norm_lt_one]
  exact (hs.comp_injective P.primeIdealPow_injective).congr fun e ↦
    idealTerm_toIdealArithmeticFunction_primeIdealPow χ P e s

/-- **The local ratios are summable over the primes.** The multiplicative specialisation of
`IdealArithmeticFunction.summable_idealTerm_primeIdealPow_one`: at a prime the ideal term *is* the
ratio `χ(P) N(P)⁻ˢ`. -/
theorem summable_div_of_summable_idealTerm
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦
      χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s :=
  (IdealArithmeticFunction.summable_idealTerm_primeIdealPow_one hs).congr fun P ↦ by
    simp [idealTerm_toIdealArithmeticFunction_primeIdealPow χ P 1 s]

/-- Absolute convergence puts every local ratio `χ(P) N(P)⁻ˢ` strictly inside the unit disc, so no
local Euler factor has a vanishing denominator. -/
theorem one_sub_div_ne_zero_of_summable_idealTerm
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) (P : HeightOneSpectrum (𝓞 K)) :
    1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s ≠ 0 := fun h ↦ by
  have hlt := norm_div_lt_one_of_summable_idealTerm χ hs P
  rw [sub_eq_zero] at h
  rw [← h] at hlt
  simp at hlt

/-- The local Euler factor of a completely multiplicative weight is the geometric closed form
`(1 - χ(P) N(P)⁻ˢ)⁻¹`. -/
theorem eulerFactor_ofMultiplicativeIdealWeight
    (P : HeightOneSpectrum (𝓞 K))
    (hP : ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖ < 1) :
    (EulerProductData.ofMultiplicativeIdealWeight χ).eulerFactor P s =
      (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹ := by
  rw [EulerProductData.eulerFactor_eq_tsum,
    EulerProductData.toIdealArithmeticFunction_ofMultiplicativeIdealWeight,
    tsum_congr fun e ↦ idealTerm_toIdealArithmeticFunction_primeIdealPow χ P e s]
  exact tsum_geometric_of_norm_lt_one hP

/-- **The Euler product of a completely multiplicative ideal weight.** -/
theorem hasProd_eulerFactor (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    HasProd (fun P : HeightOneSpectrum (𝓞 K) ↦
        (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹)
      (LSeries (normCoeff K χ.toIdealArithmeticFunction) s) := by
  have hfun : (fun P : HeightOneSpectrum (𝓞 K) ↦
      (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹) =
      fun P ↦ (EulerProductData.ofMultiplicativeIdealWeight χ).eulerFactor P s :=
    funext fun P ↦ (eulerFactor_ofMultiplicativeIdealWeight χ P
      (norm_div_lt_one_of_summable_idealTerm χ hs P)).symm
  rw [hfun]
  have hprod := (EulerProductData.ofMultiplicativeIdealWeight χ).hasProd_eulerFactor
    (s := s) (by
      simpa only [EulerProductData.toIdealArithmeticFunction_ofMultiplicativeIdealWeight] using hs)
  simpa only [EulerProductData.toIdealArithmeticFunction_ofMultiplicativeIdealWeight] using hprod



end MultiplicativeIdealWeight

/-! ### The Dedekind zeta function -/







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
# Deleting finitely many Euler factors

Restricting Euler-product data away from a finite set `S` of primes, keeping only the
coefficients of the ideals prime to `S`, replaces the local Euler factors at `S` by `1` and leaves
the others untouched. On the half-plane of absolute convergence the two `L`-series therefore
differ by the finitely many deleted factors; for a completely multiplicative weight `χ` the
restriction `χ.restrict S` divides the `L`-series by `∏ 𝔭 ∈ S, (1 - χ(𝔭) N(𝔭) ^ (-s))⁻¹`.

For the trivial weight the restriction is `ofBadPrimes S`, the indicator of the ideals prime to
`S`, and its `L`-series is the Dedekind zeta function with the Euler factors at `S` removed:

`L_S(s) = ζ_K(s) * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))`  for `Re s > 1`.

The correction factor does not vanish on `Re s > 0`, because
`|N(𝔭) ^ s| = N(𝔭) ^ (Re s) > 1` there. As `s → 1⁺`, the normalized expression
`(s - 1) L_S(s)` tends to `dedekindZeta_residue K` multiplied by the nonzero number
`∏ 𝔭 ∈ S, (1 - N(𝔭)⁻¹)`. The logarithmic derivative of `L_S` differs from that of `ζ_K` by the
finite sum `∑ 𝔭 ∈ S, log N(𝔭) / (N(𝔭) ^ s - 1)`, which is holomorphic on `Re s > 0` and in
particular across the line `Re s = 1`. This is the form in which Dirichlet series whose Euler
products omit the ramified primes, such as the trivial Galois-character series, are compared with
`ζ_K`.

## Main results

* `TauCeti.EulerProductData.eulerFactor_restrictAway_of_mem`,
  `TauCeti.EulerProductData.eulerFactor_restrictAway_of_notMem`: restricting away from `S`
  replaces the local factors at `S` by `1` and keeps the others.
* `TauCeti.EulerProductData.LSeries_restrictAway_mul_prod_eulerFactor`: multiplying the `L`-series
  of the restriction by the deleted local factors recovers the original `L`-series.
* `TauCeti.MultiplicativeIdealWeight.LSeries_restrict`: the same for a completely multiplicative
  weight, with the deleted factors in closed form.
* `TauCeti.LSeries_ofBadPrimes`: the `L`-series of the indicator of the ideals prime to `S` is
  `ζ_K(s) * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))` on `Re s > 1`.
* `TauCeti.prod_one_sub_absNorm_cpow_neg_ne_zero`: the correction factor has no zero on
  `Re s > 0`.
* `TauCeti.dedekindZeta_residue_mul_prod_one_sub_absNorm_cpow_neg_one_ne_zero`: the corrected
  residue at `s = 1` is nonzero.
* `TauCeti.tendsto_sub_one_mul_LSeries_ofBadPrimes`: the normalized right-hand limit at `s = 1`.
* `TauCeti.logDeriv_LSeries_ofBadPrimes`: the logarithmic derivative on `Re s > 1`, and
  `TauCeti.differentiableOn_sum_log_absNorm_div_cpow_sub_one`: the correction term in it is
  holomorphic on `Re s > 0`.
* `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood.LSeries_normCoeff` and
  `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood.tendsto_sub_one_mul_LSeries`: a weight that
  is a norm twist with parameter `u` on its good ideals has for `L`-series such a deleted zeta
  function read at `s - u * I`, with the corresponding pole at `s = 1 + u * I`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

 section

namespace TauCeti

open _root_.Filter
open scoped _root_.nonZeroDivisors _root_.NumberField _root_.Topology
open _root_.IsDedekindDomain (HeightOneSpectrum)

variable {K : Type*} [Field K] [NumberField K]

namespace EulerProductData

variable (D : EulerProductData K) {s : ℂ}









end EulerProductData

namespace MultiplicativeIdealWeight

variable (χ : MultiplicativeIdealWeight K) {s : ℂ}



end MultiplicativeIdealWeight

/-! ### The Dedekind zeta function with finitely many Euler factors deleted -/





/-- **The Dedekind zeta function with the Euler factors at `S` deleted.** For a finite set `S` of
primes and `Re s > 1`, the `L`-series of the indicator of the ideals prime to `S` is
`ζ_K(s) * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))`. -/
theorem LSeries_ofBadPrimes (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    LSeries (normCoeff K (MultiplicativeIdealWeight.ofBadPrimes (S : Set (HeightOneSpectrum (𝓞 K)))
        S.finite_toSet).toIdealArithmeticFunction) s =
      NumberField.dedekindZeta K s * ∏ P ∈ S, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) := by
  have hsum : Summable
      (idealTerm K (1 : MultiplicativeIdealWeight K).toIdealArithmeticFunction s) := by
    rw [MultiplicativeIdealWeight.toIdealArithmeticFunction_one]
    exact summable_idealTerm_one_iff.mpr hs
  rw [← MultiplicativeIdealWeight.one_restrict, MultiplicativeIdealWeight.LSeries_restrict _ S hsum,
    MultiplicativeIdealWeight.toIdealArithmeticFunction_one,
    ← dedekindZeta_eq_LSeries_normCoeff_one]
  congr 1
  refine Finset.prod_congr rfl fun P _ ↦ ?_
  rw [MultiplicativeIdealWeight.one_apply, if_neg P.ne_bot, Complex.cpow_neg, one_div]

/-- **The normalized right-hand limit at `s = 1` after deleting Euler factors.** As `s → 1⁺`,
`(s - 1) L_S(s)` tends to `dedekindZeta_residue K` multiplied by
`∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-1))`, which is nonzero by
`prod_one_sub_absNorm_cpow_neg_ne_zero`. -/
theorem tendsto_sub_one_mul_LSeries_ofBadPrimes (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Tendsto (fun s : ℝ ↦ (s - 1) * LSeries (normCoeff K
        (MultiplicativeIdealWeight.ofBadPrimes (S : Set (HeightOneSpectrum (𝓞 K)))
          S.finite_toSet).toIdealArithmeticFunction) s) (𝓝[>] 1)
      (𝓝 (NumberField.dedekindZeta_residue K *
        ∏ P ∈ S, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-1 : ℂ)))) := by
  have hcont : Continuous fun s : ℝ ↦ ∏ P ∈ S, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-(s : ℂ))) :=
    continuous_finsetProd _ fun P _ ↦ continuous_const.sub <|
      (Complex.continuous_ofReal.neg).const_cpow <| Or.inl P.natCast_absNorm_ne_zero
  have hprod := (hcont.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  rw [Complex.ofReal_one] at hprod
  refine ((NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K).mul hprod).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  rw [LSeries_ofBadPrimes S (by simpa using hs), mul_assoc]





/-! ### Weights that are norm twists on their good ideals -/

namespace MultiplicativeIdealWeight





end MultiplicativeIdealWeight

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
# Cancellation in ideal partial sums and the continued L-function of a weight

For a unitary ideal weight `χ` of a number field `K` of degree `d = [K : ℚ]`, the partial sums
`∑_{N(I) ≤ x} χ(I)` over the nonzero integral ideals are trivially `O(x)`, by the linear ideal
count. For nontrivial finite-order ray class characters, equidistribution among ray classes gives
the stronger bound `O(x ^ (1 - 1 / d))`. This file names that bound as a hypothesis and extracts
its analytic consequence.

* `TauCeti.HasCancellation χ` is the uniform bound
  `‖∑_{N(I) ≤ x} χ(I)‖ ≤ C * x ^ (1 - 1 / d)` for every real cutoff `x ≥ 1`, with the inclusive
  summatory function `TauCeti.idealSummatory`.
  Equivalently (`TauCeti.hasCancellation_iff_isBigO`), the partial sums are
  `O(x ^ (1 - 1 / d))` as `x → ∞`.
* `TauCeti.continuedLFunctionOfWeight χ` is the partial-summation integral
  `s * ∫_{1}^{∞} (∑_{N(I) ≤ t} χ(I)) t ^ (-(s + 1)) dt`.

It agrees with the norm-regrouped L-series of `χ` on `Re s > 1` for *every* unitary weight
(`TauCeti.continuedLFunctionOfWeight_eq_LSeries`), and under `HasCancellation χ` it is holomorphic
on `Re s > 1 - 1 / d` (`TauCeti.differentiableOn_continuedLFunctionOfWeight`); so it is an analytic
continuation of the L-series of `χ` across the line `Re s = 1`.

Both are stable under deleting finitely many Euler factors, the operation a character family
needs at the bad primes of its modulus. A one-prime recurrence relates the partial sums after
inserting a forbidden prime to two partial sums before the insertion
(`TauCeti.MultiplicativeIdealWeight.idealSummatory_restrict_insert`). Iterating this recurrence
shows that cancellation passes to the restriction (`TauCeti.HasCancellation.restrict`); on
`Re s > 1` the two continued
`L`-functions differ by the entire factor `∏ 𝔭 ∈ S, (1 - χ(𝔭) N(𝔭) ^ (-s))`
(`TauCeti.continuedLFunctionOfWeight_restrict_of_one_lt_re`), and under cancellation that identity
propagates to the whole half-plane `Re s > 1 - 1 / d`
(`TauCeti.continuedLFunctionOfWeight_restrict`).

In number-field degree greater than one, cancellation is also invariant under purely imaginary
norm twists (`TauCeti.hasCancellation_normTwist_iff`). Abel summation supplies this because the
cancellation exponent `1 - 1 / [K : ℚ]` is then positive. The degree-one case is deliberately not
claimed: the defining bound has exponent zero, while the absolute bound for the Abel integral is
logarithmic.

The continued `L`-function itself follows these operations. Conjugating the weight reflects it
in the real axis, `L(conj χ, conj s) = conj (L(χ, s))`, at every `s`
(`TauCeti.continuedLFunctionOfWeight_conj`). An imaginary norm twist by `N(I) ^ (-z)` translates
it by `z`: on `Re s > 1` for every weight
(`TauCeti.continuedLFunctionOfWeight_normTwist_of_one_lt_re`), and on the whole half-plane
`Re s > 1 - 1 / d` when both the weight and its twist have cancellation
(`TauCeti.continuedLFunctionOfWeight_normTwist`).

Cancellation is a hypothesis about the partial sums themselves. It cannot be replaced by
finiteness of the image of `χ` or of a quotient through which it factors: the values of a weight
factoring through a finite quotient of the free group on the prime ideals can be prescribed
arbitrarily prime by prime.

Nor is it automatic, and `TauCeti.not_hasCancellation_of_isNormTwistOnGood` says which weights it
excludes: those agreeing with a norm twist `I ↦ N(I) ^ (u * I)` on the ideals prime to their bad
primes. The `L`-series of such a weight is the Dedekind zeta function with finitely many Euler
factors deleted, read at `s - u * I`, so it has a pole at `s = 1 + u * I`, where cancellation
would instead make `continuedLFunctionOfWeight χ` holomorphic. The trivial weight
(`TauCeti.not_hasCancellation_one`) and its purely imaginary norm twists
(`TauCeti.not_hasCancellation_normTwist_one`) are the cases a character-family argument meets:
it must not assume cancellation for the degenerate members of its family.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1 (partial summation).
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.1.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII §6, for the partial-sum bound of finite-order
  ray class character L-series.
-/

 section

namespace TauCeti

open _root_.Filter _root_.Asymptotics _root_.IsDedekindDomain _root_.MeasureTheory
open scoped _root_.ComplexConjugate _root_.nonZeroDivisors _root_.NumberField _root_.Topology

variable {K : Type*} [Field K] [NumberField K]



/-- The cancellation exponent `1 - 1 / [K : ℚ]` is less than `1`. -/
theorem cancellationExponent_lt_one : 1 - 1 / (Module.finrank ℚ K : ℝ) < 1 := by
  have h : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  linarith [one_div_pos.mpr h]











/-!
### Deleting finitely many Euler factors
-/



/-- **Cancellation bounds the partial sums of the norm coefficients**, in the `O(n ^ r)` form of
Mathlib's `LSeries_eq_mul_integral`. -/
theorem HasCancellation.isBigO_sum_normCoeff {χ : UnitaryIdealWeight K} (hχ : HasCancellation χ) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, normCoeff K χ.toIdealArithmeticFunction k) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨C, hC⟩ := hχ
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [← Nat.floor_natCast (R := ℝ) n, ← idealSummatory_eq_sum_Icc_normCoeff, Nat.floor_natCast,
    Real.norm_of_nonneg (by positivity)]
  exact hC n (by exact_mod_cast hn)



/-- The continued L-function as the integral of Mathlib's `LSeries_eq_mul_integral`, over the
partial sums of the norm coefficients. -/
theorem continuedLFunctionOfWeight_eq_mul_integral (χ : UnitaryIdealWeight K) (s : ℂ) :
    continuedLFunctionOfWeight χ s = s * ∫ t in Set.Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, normCoeff K χ.toIdealArithmeticFunction k) *
        (t : ℂ) ^ (-(s + 1)) := by
  simp only [continuedLFunctionOfWeight, idealSummatory_eq_sum_Icc_normCoeff]

/-- **The continued L-function is the L-series on `Re s > 1`.** For every unitary weight, with or
without cancellation, `continuedLFunctionOfWeight χ` agrees with the `LSeries` of the norm
coefficients of `χ` to the right of `1`, where that series converges absolutely. -/
theorem continuedLFunctionOfWeight_eq_LSeries (χ : UnitaryIdealWeight K) {s : ℂ}
    (hs : 1 < s.re) :
    continuedLFunctionOfWeight χ s = LSeries (normCoeff K χ.toIdealArithmeticFunction) s := by
  rw [continuedLFunctionOfWeight_eq_mul_integral]
  refine (LSeries_eq_mul_integral' _ zero_le_one (by simpa using hs) ?_).symm
  refine (IsBigO.of_bound 1 (Eventually.of_forall fun n ↦ ?_)).trans
    (isBigO_sum_norm_normCoeff_one K)
  rw [one_mul, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _),
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
  exact Finset.sum_le_sum fun k _ ↦
    UnitaryIdealWeight.norm_normCoeff_le_norm_normCoeff_one K χ k

/-- **Cancellation continues the L-series of a weight.** If `χ` has cancellation, its continued
L-function is holomorphic on the half-plane `Re s > 1 - 1 / [K : ℚ]`, which contains the line
`Re s = 1`. -/
theorem differentiableOn_continuedLFunctionOfWeight {χ : UnitaryIdealWeight K}
    (hχ : HasCancellation χ) :
    DifferentiableOn ℂ (continuedLFunctionOfWeight χ)
      {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} := by
  rw [funext (continuedLFunctionOfWeight_eq_mul_integral χ)]
  exact LSeries.differentiableOn_mul_integral_of_isBigO _ hχ.isBigO_sum_normCoeff

/-- **Deleting finitely many Euler factors, to the right of `1`.** Where the norm-regrouped series
converge absolutely, restricting a unitary weight away from a finite set `S` of primes multiplies
its continued `L`-function by the reciprocals `∏ 𝔭 ∈ S, (1 - χ(𝔭) N(𝔭) ^ (-s))` of the deleted
local factors. -/
theorem continuedLFunctionOfWeight_restrict_of_one_lt_re (χ : UnitaryIdealWeight K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    continuedLFunctionOfWeight
        (χ.restrict (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet) s =
      continuedLFunctionOfWeight χ s *
        ∏ 𝔭 ∈ S, (1 - χ.1 𝔭.asIdeal / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s) := by
  rw [continuedLFunctionOfWeight_eq_LSeries _ hs, continuedLFunctionOfWeight_eq_LSeries _ hs,
    UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
    UnitaryIdealWeight.toIdealArithmeticFunction_eq_val, UnitaryIdealWeight.val_restrict]
  exact χ.1.LSeries_restrict S (by
    rw [← UnitaryIdealWeight.toIdealArithmeticFunction_eq_val]
    exact summable_idealTerm_of_unitary_of_one_lt_re χ hs)



/-!
### Conjugation and imaginary norm twists
-/







/-!
### The rejection test: weights that are norm twists on their good ideals
-/









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
namespace TauCeti.IdealArithmeticFunction
end TauCeti.IdealArithmeticFunction
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The Euler product over the primes of a number field, in exponential form

Mathlib's `EulerProduct.exp_tsum_primes_log_eq_tsum` writes the Euler product of a completely
multiplicative `f : ℕ →*₀ ℂ` as `exp (∑' p, -log (1 - f p))`. This file is the ideal-indexed
analogue, over the height-one primes of the ring of integers of a number field, mirroring the way
`TauCeti.MultiplicativeIdealWeight.hasProd_eulerFactor` mirrors Mathlib's product form.

The logarithm is taken factor by factor, using the principal value: absolute convergence of the
ideal-indexed series forces each local ratio into the open unit disc, where `Complex.log (1 - ·)`
is defined without choosing anything.

**What this does not give.** `exp` is not injective, so an identity of the form `exp t = L`
determines `t` only modulo `2πi ℤ`; these theorems therefore do not exhibit a logarithm *of* the
`L`-series, and in particular are not a holomorphic branch on a region.
`TauCeti.MultiplicativeIdealWeight.LSeries_ne_zero_of_summable_idealTerm` supplies nonvanishing
pointwise, wherever the ideal-indexed series converges absolutely; a branch needs more than that —
a simply connected zero-free region on which to choose one — and is not constructed here.

## Main results

* `TauCeti.MultiplicativeIdealWeight.summable_neg_log_one_sub`: summability of the
  prime-indexed logarithm sum wherever the ideal-indexed series converges absolutely.
* `TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries`: the `L`-series as the
  exponential of a sum of principal logarithms over the primes.
* `TauCeti.MultiplicativeIdealWeight.tsum_prime_pow_eq_tsum_neg_log_one_sub`: that sum re-indexed
  by a prime and an exponent, as an identity of complex numbers.
* `TauCeti.MultiplicativeIdealWeight.exp_tsum_prime_pow_eq_LSeries`: the exponential form of the
  re-indexed sum.
-/

 section

namespace TauCeti

open _root_.Complex _root_.IsDedekindDomain

open scoped _root_.NumberField

namespace MultiplicativeIdealWeight

open _root_.TauCeti.IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K) {s : ℂ}

/-- The prime-indexed sum of principal logarithms converges whenever the ideal-indexed series
of a multiplicative ideal weight converges absolutely. -/
theorem summable_neg_log_one_sub
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    Summable (fun P : HeightOneSpectrum (𝓞 K) ↦
      -log (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)) :=
  (Summable.clog_one_sub (χ.summable_div_of_summable_idealTerm hs)).neg

/-- **The Euler product in exponential form.** For a completely multiplicative ideal weight whose
ideal-indexed series converges absolutely at `s`, the `L`-series is the exponential of the sum of
principal logarithms `-log (1 - χ(P) N(P)⁻ˢ)` over the height-one primes.

The sum is not thereby a logarithm of the `L`-series: `exp` identifies it only modulo `2πi ℤ`.
This is the number-field analogue of Mathlib's `EulerProduct.exp_tsum_primes_log_eq_tsum`, and
carries the same limitation. -/
theorem exp_tsum_neg_log_one_sub_eq_LSeries
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    exp (∑' P : HeightOneSpectrum (𝓞 K),
        -log (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)) =
      LSeries (normCoeff K χ.toIdealArithmeticFunction) s := by
  have hne := χ.one_sub_div_ne_zero_of_summable_idealTerm hs
  have H := (χ.summable_neg_log_one_sub hs).hasSum.cexp.tprod_eq
  simp only [Function.comp_apply, exp_neg, exp_log (hne _)] at H
  exact H.symm.trans (χ.hasProd_eulerFactor hs).tprod_eq

/-- **The prime-power sum is the prime-indexed logarithm sum.**  Substituting the Taylor series of
`-log (1 - ·)` at each prime and regrouping over the primes identifies the two sums *as complex
numbers*, before any exponential is taken.  This is the statement a consumer needs in order to
rewrite one into the other; the exponential form below follows from it. -/
theorem tsum_prime_pow_eq_tsum_neg_log_one_sub
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ s) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1) =
      ∑' P : HeightOneSpectrum (𝓞 K),
        -log (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) :=
  tsum_taylorSeries_neg_log
    (r := fun P : HeightOneSpectrum (𝓞 K) ↦ χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)
    (χ.summable_div_of_summable_idealTerm hs) (χ.norm_div_lt_one_of_summable_idealTerm hs)

/-- **The Euler product expanded over prime powers.**  The `L`-series is the exponential of the
sum over pairs `(P, e)` of a prime and an exponent.  The caveat above applies unchanged: `exp` is
not injective, so this identifies the double sum only modulo `2πi ℤ` and does not exhibit a
logarithm of the `L`-series. -/
theorem exp_tsum_prime_pow_eq_LSeries
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    exp (∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ s) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1)) =
      LSeries (normCoeff K χ.toIdealArithmeticFunction) s := by
  rw [χ.tsum_prime_pow_eq_tsum_neg_log_one_sub hs, χ.exp_tsum_neg_log_one_sub_eq_LSeries hs]

end MultiplicativeIdealWeight

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

/-- No ramified prime carries an Artin class: the fibres avoid `ramifiedPrimes K L`. -/
theorem frobeniusPrimeSet_subset_compl_ramifiedPrimes (C : ConjClasses (L ≃ₐ[K] L)) :
    frobeniusPrimeSet K L C ⊆ (↑(ramifiedPrimes K L))ᶜ := fun 𝔭 h hmem ↦
  (mem_ramifiedPrimes_iff 𝔭).mp (Finset.mem_coe.mp hmem) fun Q _ _ ↦
    isUnramifiedAt_of_mem_frobeniusPrimeSet h Q







section IsoOfExtensions

variable {L' : Type*} [Field L'] [NumberField L'] [Algebra K L'] [IsGalois K L']



end IsoOfExtensions

section RestrictNormal

variable {M : Type*} [Field M] [NumberField M] [Algebra K M] [Algebra M L] [IsScalarTower K M L]
  [IsGalois K M]



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
namespace TauCeti
end TauCeti
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The ideal weight of a Galois character

For a finite Galois extension `L / K` of number fields and a character `χ : Gal(L/K) →* ℂˣ`, this
file builds the *canonical ideal weight* `galoisCharacterWeight χ`: the completely multiplicative
function on the ideals of `𝓞 K` whose value at a height-one prime `𝔭` is `χ (Frob 𝔭)` when `𝔭` is
unramified in `L`, and `0` when `𝔭` ramifies. Since `Gal(L/K)` is finite those unramified values
are roots of unity, so the same weight is packaged a second time as a
`TauCeti.UnitaryIdealWeight K`.

Nothing here assumes that `L / K` is cyclotomic: the construction needs only `[IsGalois K L]`, and
the character is an arbitrary degree-one complex character of the Galois group. The Dirichlet
weight is the specialisation `L / K = ℚ(ζ_m) / ℚ`, where the cyclotomic character identifies
`Gal(ℚ(ζ_m)/ℚ)` with `(ZMod m)ˣ` and `χ` is a Dirichlet character mod `m`. Over a general base `K`
that character is still injective but need not be surjective: restriction identifies
`Gal(K(ζ_m)/K)` with the subgroup of `(ZMod m)ˣ` fixing `K ∩ ℚ(ζ_m)`, and that subgroup is all of
`(ZMod m)ˣ` exactly when `K ∩ ℚ(ζ_m) = ℚ`. The declarations are named for the generality they
actually have.

The weight is **total**, and that is a design constraint rather than a convenience: a weight
specified only away from ramification leaves its values at the bad primes unconstrained, so the
Euler product and the orthogonality identities would not pin it down. Vanishing at the ramified
primes is what makes the ramified Euler factors drop out as `(1 - 0)⁻¹ = 1`.

## Main definitions

* `MonoidHom.galoisCharacterWeight`: the weight of `χ`, packaged as a
  `TauCeti.MultiplicativeIdealWeight K`.
* `MonoidHom.galoisCharacterUnitaryWeight`: the same weight packaged as a
  `TauCeti.UnitaryIdealWeight K`, its values having modulus `1` away from the ramified primes.

## Main results

* `MonoidHom.galoisCharacterWeight_apply_of_unramified`: at an unramified height-one prime the
  weight is `χ` of the Artin symbol.
* `MonoidHom.galoisCharacterWeight_apply_eq_zero_iff`: the weight vanishes at a height-one prime
  exactly when that prime ramifies in `L`.
* `MonoidHom.badPrimes_galoisCharacterWeight`: the bad primes of the weight are exactly the
  ramified primes.
* `MonoidHom.galoisCharacterWeight_one`: the weight of the trivial character is the indicator of
  the ideals prime to the ramified primes, so its `L`-series is the Dedekind zeta function with the
  ramified Euler factors deleted.
* `MonoidHom.galoisCharacterWeight_mul`: the weight of a product of characters is the product of
  their weights.
* `MonoidHom.val_galoisCharacterUnitaryWeight`: the unitary packaging has the same underlying
  weight.
* `MonoidHom.norm_galoisCharacterWeight_le_one`: the weight of a Galois character is bounded by
  `1`.
* `MonoidHom.summable_idealTerm_galoisCharacterWeight`: the ideal series of a Galois character
  converges absolutely on `Re s > 1`.

## Implementation notes

The weight is packaged as a `TauCeti.MultiplicativeIdealWeight K` rather than as a bare function
`Ideal (𝓞 K) → ℂ`, so that the totality above is expressed in the carrier's own `badPrimes` API:
the bad primes of `χ.galoisCharacterWeight` are exactly `ramifiedPrimes K L`.

`TauCeti.UnitaryIdealWeight K` is the subtype of those multiplicative weights whose values have
modulus `1` away from the bad primes, so the unitary packaging records strictly more than the
multiplicative one and is not a replacement for it: `galoisCharacterWeight` remains the definition
everything else is stated about, and `val_galoisCharacterUnitaryWeight` is the bridge. Unitarity is
a property of the weight rather than of `χ`, so no hypothesis constrains `χ` itself to the unit
circle.

## References

Adapted from `galoisCharacterOnIdeal`, `galoisCharacterOnIdeal_mul` and
`norm_galoisCharacterOnIdeal_le_one` in `CebotarevDensity/ZetaProduct.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, following Sharifi,
*Algebraic Number Theory*, Notation 7.1.17. The factorization-product definition and the
`Multiset.map_add`/`Multiset.prod_add` multiplicativity argument are the source's; the
`MultiplicativeIdealWeight` packaging and the `artinSymbol` totalization are not the source's and
are new here. The source likewise names the construction for a general Galois character.
-/

 section

open scoped _root_.NumberField

open _root_.IsDedekindDomain (HeightOneSpectrum)

open _root_.UniqueFactorizationMonoid
open _root_.TauCeti

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

















end NumberField.Chebotarev

open _root_.NumberField _root_.NumberField.Chebotarev

namespace MonoidHom

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]











/-- **The weight of the trivial character** is the indicator of the ideals prime to the ramified
primes. Its `L`-series is therefore the Dedekind zeta function of `K` with the Euler factors at the
ramified primes deleted (`TauCeti.LSeries_ofBadPrimes`). -/
@[simp]
theorem galoisCharacterWeight_one :
    galoisCharacterWeight (L := L) (1 : (L ≃ₐ[K] L) →* ℂˣ) =
      TauCeti.MultiplicativeIdealWeight.ofBadPrimes (ramifiedPrimes K L : Set _)
        (ramifiedPrimes K L).finite_toSet := by
  classical
  refine TauCeti.MultiplicativeIdealWeight.ext_heightOneSpectrum fun 𝔭 ↦ ?_
  rw [TauCeti.MultiplicativeIdealWeight.ofBadPrimes_apply, Ideal.isPrimeTo_asIdeal_iff,
    Finset.mem_coe]
  by_cases h : 𝔭 ∈ ramifiedPrimes K L
  · simp only [h, not_true_eq_false, ↓reduceIte]
    exact (galoisCharacterWeight_apply_eq_zero_iff _ 𝔭).mpr h
  · simp only [h, not_false_eq_true, ↓reduceIte]
    rw [galoisCharacterWeight_apply_of_unramified _ 𝔭
        (not_not.mp (mt (mem_ramifiedPrimes_iff 𝔭).mpr h)), MonoidHom.one_apply, Units.val_one]





/-- The unitary packaging has the same underlying weight. -/
@[simp]
theorem val_galoisCharacterUnitaryWeight (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    (galoisCharacterUnitaryWeight (L := L) χ).1 = galoisCharacterWeight (L := L) χ := by
  simp [galoisCharacterUnitaryWeight]



/-- The ideal series of a Galois character weight converges absolutely on `Re s > 1`. -/
theorem summable_idealTerm_galoisCharacterWeight (χ : (L ≃ₐ[K] L) →* ℂˣ) {s : ℂ}
    (hs : 1 < s.re) :
    Summable (idealTerm K χ.galoisCharacterWeight.toIdealArithmeticFunction s) :=
  by simpa only [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
      val_galoisCharacterUnitaryWeight] using
    summable_idealTerm_of_unitary_of_one_lt_re χ.galoisCharacterUnitaryWeight hs

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
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Ray class characters

A ray class character of a modulus `𝔪` is a multiplicative character of its finite ray class
group with values in the complex units.  Composing with `idealClass 𝔪` evaluates it on the
nonzero integral ideals prime to the finite part of `𝔪`; the coprimality proof remains in the
domain because `idealClass 𝔪` is defined only on those ideals.

When `𝔪 ∣ 𝔫`, pullback along the surjective transition `classMap : Cl_𝔫 → Cl_𝔪` induces a
character of the larger modulus.  These pullbacks are injective, compose along chains of moduli,
and agree with the inclusion of integral ideals prime to the larger modulus.  This is the finite
character API used in ray-class counting and in the factorization of cyclotomic Galois
characters.

## Main definitions

* `TauCeti.GlobalNumberFields.RayClassCharacter`: multiplicative complex-unit characters of a
  ray class group;
* `TauCeti.GlobalNumberFields.RayClassCharacter.onIdeals`: evaluation on integral ideals prime
  to the modulus;
* `TauCeti.GlobalNumberFields.RayClassCharacter.induced`: pullback of a character along a change
  of modulus.

## Main results

* `TauCeti.GlobalNumberFields.RayClassCharacter.ext`: a ray class character is
  determined by its values on integral ideals;
* `TauCeti.GlobalNumberFields.RayClassCharacter.induced_injective`: increasing the modulus does
  not identify distinct characters;
* `TauCeti.GlobalNumberFields.RayClassCharacter.onIdeals_induced`: change of modulus commutes
  with evaluation on ideals.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VII, §1.
-/

 section

open scoped _root_.NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]



namespace RayClassCharacter

variable {𝔪 𝔫 𝔬 : Modulus K}



/-- Evaluating a ray class character on an ideal is evaluation at the ideal's ray class. -/
@[simp]
theorem onIdeals_apply (χ : RayClassCharacter 𝔪) (I : integralIdealsPrimeTo 𝔪) :
    χ.onIdeals I = χ (idealClass 𝔪 I) :=
  by simp [onIdeals]

















end RayClassCharacter

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
private theorem galoisCharacterWeight_asIdeal_eq_cyclotomicArtin (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∈ integralIdealsPrimeTo (cyclotomicModulus K m)) :
    galoisCharacterWeight (L := F) χ v.asIdeal =
      (χ (cyclotomicArtin K F m (idealClass _ ⟨v.asIdeal, hv⟩)) : ℂ) := by
  have hur : ∀ (Q : Ideal (𝓞 F)) [Q.IsPrime] [Q.LiesOver v.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q := fun Q _ _ ↦
    isUnramifiedAt_of_notMem_cyclotomicModulus_support F m
      (mem_cyclotomicModulus_support_iff.not.mpr
        (asIdeal_mem_integralIdealsPrimeTo_cyclotomicModulus_iff.mp hv)) Q
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 F)))
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
  have := IsCyclotomicExtension.isMulCommutative {m} K F
  -- `Gal(F/K)` is abelian, so the Artin symbol at `v` is the singleton class of `σ`
  rw [galoisCharacterWeight_apply_of_unramified χ v hur,
    cyclotomicArtin_idealClass_of_isArithFrobAt F m v hv Q hσ,
    isConj_iff_eq.mp (ConjClasses.mk_eq_mk_iff_isConj.mp ((Quotient.out_eq _).trans
      (artinSymbol_eq_mk_of_isArithFrobAt v.asIdeal hur Q σ hσ)))]

/-- **The ideal weight of a cyclotomic Galois character is a ray class character.** For a
character `χ` of `Gal(F/K)` with `F = K(μ_m)`, the ideal weight `galoisCharacterWeight χ` agrees,
on the integral ideals prime to `m`, with the ray class character `χ ∘ cyclotomicArtin K F m` of
`cyclotomicModulus K m`. -/
theorem galoisCharacterWeight_eq_onIdeals_cyclotomicArtin (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (I : integralIdealsPrimeTo (cyclotomicModulus K m)) :
    galoisCharacterWeight (L := F) χ (I : Ideal (𝓞 K)) =
      (RayClassCharacter.onIdeals (χ.comp (cyclotomicArtin K F m)) I : ℂ) := by
  -- both sides are multiplicative in `I`, and they agree on the primes `v ∤ m`
  let f : integralIdealsPrimeTo (cyclotomicModulus K m) →* ℂ :=
    (galoisCharacterWeight (L := F) χ).toMonoidWithZeroHom.toMonoidHom.comp
      (integralIdealsPrimeTo (cyclotomicModulus K m)).subtype
  let g : integralIdealsPrimeTo (cyclotomicModulus K m) →* ℂ :=
    (Units.coeHom ℂ).comp (RayClassCharacter.onIdeals (χ.comp (cyclotomicArtin K F m)))
  have hfg : f = g := integralIdealsAway_hom_ext fun v hv ↦ by
    simpa [f, g, TauCeti.MultiplicativeIdealWeight.coe_toMonoidWithZeroHom] using
      galoisCharacterWeight_asIdeal_eq_cyclotomicArtin χ v hv
  exact DFunLike.congr_fun hfg I

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
# Character sums over the integral ideals of bounded norm

Let `𝔪` be a modulus of a number field `K` and `χ` a ray class character of `𝔪`.  This file
introduces `rayClassCharacterPartialSum 𝔪 χ x`, the sum of `χ` over the nonzero integral ideals
prime to the finite part of `𝔪` whose norm is at most `x`, and identifies it with the
`χ`-weighted combination of the ray class counting functions.

The sum ranges over ideals, not over chosen class representatives.  Regrouping it by ray class is
exactly the partition `idealClassSigmaEquiv`, and on each fibre `χ` is constant, so each class
contributes its counting function scaled by the single value `χ` takes there.

## Main definitions

* `TauCeti.GlobalNumberFields.rayClassCharacterPartialSum`: the partial sum of a ray class
  character over the integral ideals of bounded norm.

## Main results

* `TauCeti.GlobalNumberFields.rayClassCharacterPartialSum_eq_sum`: the partial sum is
  `∑ c, χ c * rayClassIdealCountingFunction 𝔪 c x`.
-/

 section

namespace TauCeti.GlobalNumberFields

open scoped _root_.NumberField

variable {K : Type*} [Field K] [NumberField K]



open scoped Classical in
/-- **The partial sum as the `finsum` defining it.**  The rewrite rule turning
`rayClassCharacterPartialSum` into the sum of `χ.onIdeals` over the integral ideals prime to `𝔪`
of norm at most `x`. -/
theorem rayClassCharacterPartialSum_def (𝔪 : Modulus K) (χ : RayClassCharacter 𝔪) (x : ℝ) :
    rayClassCharacterPartialSum 𝔪 χ x =
      ∑ᶠ I : {I : integralIdealsPrimeTo 𝔪 // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x},
        (χ.onIdeals (I : integralIdealsPrimeTo 𝔪) : ℂ) := by
  rw [rayClassCharacterPartialSum, summatory_apply, ← finsum_mem_coe_finset, coe_normLE]
  exact (finsum_set_coe_eq_finsum_mem _).symm



end TauCeti.GlobalNumberFields

end
end

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
namespace TauCeti.GlobalNumberFields
end TauCeti.GlobalNumberFields
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Cancellation for the ideal weight of a cyclotomic Galois character

Let `F = K(μ_m)` be an `m`-th cyclotomic extension of a number field `K` and `χ` a character of
`Gal(F/K)` whose ray class character `χ ∘ cyclotomicArtin K F m` of `cyclotomicModulus K m` is
nontrivial. This file provides cancellation for the ideal weight `galoisCharacterUnitaryWeight χ`
with its Euler factors at the primes dividing `m` deleted: its ideal partial sums are
`O(x ^ (1 - 1 / [K : ℚ]))`. At such a prime the weight can be a root of unity rather than `0` (the
prime may be unramified in `F`), so the restricted weight is the one that agrees with the ray class
character.

## Main results

* `MonoidHom.hasCancellation_restrict_galoisCharacterUnitaryWeight`: the weight restricted away
  from the primes dividing `m` has cancellation.
-/

 section

open _root_.IsDedekindDomain _root_.TauCeti _root_.TauCeti.GlobalNumberFields _root_.NumberField.Chebotarev
open scoped _root_.nonZeroDivisors _root_.NumberField

namespace MonoidHom

variable {K : Type*} [Field K] [NumberField K] {F : Type*} [Field F] [NumberField F]
  [Algebra K F] {m : ℕ} [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

-- The ideal partial sums of the Galois weight with the Euler factors at the primes dividing `m`
-- deleted are the partial sums of the ray class character `χ ∘ cyclotomicArtin K F m`.
private theorem idealSummatory_restrict_galoisCharacterUnitaryWeight (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (x : ℝ) :
    idealSummatory K ((galoisCharacterUnitaryWeight (L := F) χ).restrict
        ((cyclotomicModulus K m).support : Set (HeightOneSpectrum (𝓞 K)))
        (cyclotomicModulus K m).support.finite_toSet).toIdealArithmeticFunction x =
      rayClassCharacterPartialSum (cyclotomicModulus K m) (χ.comp (cyclotomicArtin K F m)) x := by
  classical
  set 𝔪 := cyclotomicModulus K m
  have hmem (J : Ideal (𝓞 K)) : J ∈ integralIdealsPrimeTo 𝔪 ↔ J.IsPrimeTo 𝔪.support :=
    NumberFieldArithmetic.mem_integralIdealsAway_iff.trans Ideal.isPrimeTo_iff.symm
  let e : integralIdealsPrimeTo 𝔪 → (Ideal (𝓞 K))⁰ := fun I ↦
    ⟨I, mem_nonZeroDivisors_of_ne_zero ((hmem I).mp I.2).ne_bot⟩
  have hsum : rayClassCharacterPartialSum 𝔪 (χ.comp (cyclotomicArtin K F m)) x =
      ∑ I ∈ normLE (fun I : integralIdealsPrimeTo 𝔪 ↦ Ideal.absNorm (I : Ideal (𝓞 K))) x,
        (RayClassCharacter.onIdeals (χ.comp (cyclotomicArtin K F m)) I : ℂ) := by
    rw [rayClassCharacterPartialSum_def, ← finsum_mem_coe_finset, coe_normLE]
    exact finsum_set_coe_eq_finsum_mem
      (f := fun I ↦ (RayClassCharacter.onIdeals (χ.comp (cyclotomicArtin K F m)) I : ℂ)) _
  rw [hsum, idealSummatory_apply]
  refine (Finset.sum_of_injOn e (fun I _ J _ h ↦ Subtype.ext (by simpa [e] using h))
    (fun I hI ↦ by simpa [e] using hI) (fun J hJ hJe ↦ ?_) (fun I _ ↦ ?_)).symm
  · simpa using fun hJ𝔪 ↦ absurd ⟨⟨J, (hmem J).mpr hJ𝔪⟩, by simpa using hJ, rfl⟩ hJe
  · simpa [e, 𝔪, (hmem I).mp I.2] using (galoisCharacterWeight_eq_onIdeals_cyclotomicArtin χ I).symm

/-- **Cancellation for a cyclotomic Galois character, away from the level.** For `F = K(μ_m)`
and a character `χ` of `Gal(F/K)` whose ray class character `χ ∘ cyclotomicArtin K F m` is
nontrivial, the ideal weight of `χ` with the Euler factors at the primes dividing `m` deleted has
cancellation. -/
theorem hasCancellation_restrict_galoisCharacterUnitaryWeight (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (hχ : χ.comp (cyclotomicArtin K F m) ≠ 1) :
    HasCancellation ((galoisCharacterUnitaryWeight (L := F) χ).restrict
      ((cyclotomicModulus K m).support : Set (HeightOneSpectrum (𝓞 K)))
      (cyclotomicModulus K m).support.finite_toSet) := by
  simpa [hasCancellation_iff_isBigO, idealSummatory_restrict_galoisCharacterUnitaryWeight] using
    isBigO_rayClassCharacterPartialSum _ _ hχ

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
# Character orthogonality for the ideal weight of a Galois character

For a finite **abelian** Galois extension `L / K` of number fields, summing `(χ σ)⁻¹` against the
ideal weight `MonoidHom.galoisCharacterWeight χ` over all characters `χ : Gal(L/K) →* ℂˣ` selects
one Frobenius fibre: at a height-one prime `𝔭` unramified in `L` the sum is `#Gal(L/K)` when the
Frobenius at `𝔭` is `σ`, and `0` otherwise. At a ramified prime it is `0`, because every summand is.

What the identity buys is a change of index: an indicator of the single condition `Frob 𝔭 = σ`
becomes a sum over the character group, in which each character contributes an ideal weight that is
completely multiplicative, and so is open to Euler-product and Dirichlet-series methods.

## Main results

* `AlgEquiv.sum_inv_mul_galoisCharacterWeight_apply_of_unramified`: the orthogonality identity at
  an unramified height-one prime, selecting the fibre of a chosen `σ`.
* `AlgEquiv.sum_inv_mul_galoisCharacterWeight_pow_apply_of_unramified`: the same identity for the
  `j`-th power of the weight, selecting the primes whose Frobenius has `j`-th power `σ`.
* `AlgEquiv.sum_inv_mul_galoisCharacterWeight_apply_eq_zero_of_mem_ramifiedPrimes`: the sum
  vanishes at a ramified prime, for the trivial reason that every summand does.

## Implementation notes

The inverse sits on the tag `σ`, never on the Frobenius argument. Without it the sum is
`∑ χ, χ (σ * Frob 𝔭)`, the indicator of `Frob 𝔭 = σ⁻¹`, which is a different fibre whenever `σ` is
not an involution.

Commutativity enters as `[IsMulCommutative (L ≃ₐ[K] L)]`, a `Prop`-class, rather than as a
`CommGroup` instance argument: `L ≃ₐ[K] L` already carries a `Group` instance, and a second
bundled group structure on the same type would be a diamond. Mathlib supplies the bundled form
from the mixin as a `scoped instance` in the `IsMulCommutative` namespace, deliberately kept out of
global synthesis, so the proofs open that scope. The abelian hypothesis is what
`CommGroup.sum_inv_mul_monoidHom_apply_eq_ite` requires; `Gal(K(ζ_m)/K)` satisfies it by
`IsCyclotomicExtension.Aut.commGroup`.

The sum ranges over the full character group, whose cardinality equals `Nat.card (L ≃ₐ[K] L)` by
Mathlib's duality for finite abelian groups; that equality is what puts `Nat.card (L ≃ₐ[K] L)` on
the right rather than the cardinality of the dual.

## References

The orthogonality relation and its use to select a Frobenius fibre are adapted from
`sum_galoisCharacter_mul_inv_eq` and the pair `character_orthogonality_cyclotomic_eq` /
`character_orthogonality_cyclotomic_ne` in `CebotarevDensity/Cyclotomic.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `55a89985d47a3befcf6069aca1da250ff088b5c7`, which attributes the
argument to Sharifi, *Algebraic Number Theory*, 7.2.1 step (iii), p. 142. The statements here are
in `if`-normal form rather than split into matching and non-matching cases, are taken at the level
of the ideal weight rather than of `χ (Frob 𝔭)` directly, and hold for a general abelian extension
rather than a cyclotomic one.
-/

 section

open scoped _root_.NumberField

open _root_.IsDedekindDomain (HeightOneSpectrum)

open _root_.NumberField _root_.NumberField.Chebotarev

namespace AlgEquiv

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]



open scoped Classical IsMulCommutative in
/-- **Character orthogonality for a power of the Galois character weight.** For `L / K` abelian,
`σ` a chosen element of `Gal(L/K)`, `𝔭` a height-one prime unramified in `L` and `j` a natural
number, summing `(χ σ)⁻¹` against the `j`-th power of the weight at `𝔭` gives `#Gal(L/K)` when
the `j`-th power of the Frobenius at `𝔭` is `σ`, and `0` otherwise.

This is the form the prime-power terms of a logarithmic derivative need: the weight at `𝔭 ^ j` is
`χ (Frob 𝔭) ^ j = χ (Frob 𝔭 ^ j)`, so the power lands on the Frobenius argument and the inverse
stays on the tag. -/
theorem sum_inv_mul_galoisCharacterWeight_pow_apply_of_unramified
    [IsMulCommutative (L ≃ₐ[K] L)] (σ : L ≃ₐ[K] L) (𝔭 : HeightOneSpectrum (𝓞 K))
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) (j : ℕ) :
    haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
    ∑ χ : (L ≃ₐ[K] L) →* ℂˣ,
          (((χ σ)⁻¹ : ℂˣ) : ℂ) * MonoidHom.galoisCharacterWeight (L := L) χ 𝔭.asIdeal ^ j =
      if (artinSymbol (L := L) 𝔭.asIdeal hur).out ^ j = σ then (Nat.card (L ≃ₐ[K] L) : ℂ)
      else 0 := by
  have hexp : Monoid.exponent (L ≃ₐ[K] L) ≠ 0 := Monoid.exponent_ne_zero_of_finite
  have : NeZero ((Monoid.exponent (L ≃ₐ[K] L) : ℕ) : ℂ) := ⟨Nat.cast_ne_zero.mpr hexp⟩
  calc ∑ χ : (L ≃ₐ[K] L) →* ℂˣ,
          (((χ σ)⁻¹ : ℂˣ) : ℂ) * MonoidHom.galoisCharacterWeight (L := L) χ 𝔭.asIdeal ^ j
      = ∑ χ : (L ≃ₐ[K] L) →* ℂˣ,
          (((χ σ)⁻¹ : ℂˣ) : ℂ) * ((χ ((artinSymbol (L := L) 𝔭.asIdeal hur).out ^ j) : ℂˣ) : ℂ) :=
        Finset.sum_congr rfl fun χ _ ↦ by
          rw [MonoidHom.galoisCharacterWeight_apply_of_unramified χ 𝔭 hur, map_pow,
            Units.val_pow_eq_pow_val]
    _ = _ := CommGroup.sum_inv_mul_monoidHom_apply_eq_ite _ _



end AlgEquiv

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
# The continued L-series of a cyclotomic Galois character

For a finite Galois extension `F / K` of number fields and a character `χ` of `Gal(F/K)`,
`cyclotomicCharacterSeriesC K F χ` is a holomorphic continuation of the `L`-series of the ideal
weight `galoisCharacterWeight χ` to the half-plane `Re s > 1 - 1 / [K : ℚ]` when one exists, and
the `L`-series itself otherwise. For every `χ` it agrees with the `L`-series on `Re s > 1`.

For a cyclotomic extension `F = K(μ_m)` and a nontrivial character `χ`, the continuation exists,
so the series is analytic at `s = 1`, and its value at `s = 1` is nonzero. For the trivial
character the series is the Dedekind zeta function of `K` with the Euler factors at the ramified
primes deleted, which continues across `Re s = 1` apart from a single simple pole at `s = 1`.

## Main definitions

* `NumberField.Chebotarev.cyclotomicCharacterSeriesC`: the continued `L`-series of a Galois
  character.

## Main results

* `NumberField.Chebotarev.cyclotomicCharacterSeriesC_eq_LSeries`: on `Re s > 1` it is the
  `L`-series of `galoisCharacterWeight χ`.
* `NumberField.Chebotarev.logDeriv_cyclotomicCharacterSeriesC`: the logarithmic derivative
  agrees with that of the character `L`-series on `Re s > 1`.
* `NumberField.Chebotarev.differentiableOn_cyclotomicCharacterSeriesC`: for `F = K(μ_m)` and
  `χ` nontrivial it is holomorphic on `Re s > 1 - 1 / [K : ℚ]`.
* `NumberField.Chebotarev.analyticAt_cyclotomicCharacterSeriesC_one`: for `F = K(μ_m)` and `χ`
  nontrivial it is analytic at `s = 1`.
* `NumberField.Chebotarev.cyclotomicCharacterSeriesC_ne_zero_at_one`: for `F = K(μ_m)` and `χ`
  nontrivial it is nonzero at `s = 1`.

## References

* The nonvanishing argument at `s = 1`, in which the logarithm of the product of the `L`-series
  over all characters is a series with nonnegative coefficients that is unbounded as `s → 1⁺`, is
  analogous to `Chebotarev.artinLSeries_one_ne_zero` in AINTLIB (`github.com/CBirkbeck/aintlib`
  at commit `8102fa09bbf570f3e991adfdb2d6d70b48cb5b5e`, Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/ZetaProduct.lean`, which proves the nonvanishing at
  `s = 1` of the Artin `L`-series of a nontrivial character of `Gal(K(μ_m)/K)`.
-/

 section

open _root_.Filter _root_.IsDedekindDomain _root_.NumberField _root_.TauCeti
open scoped _root_.Topology

namespace NumberField.Chebotarev
end NumberField.Chebotarev
section NumberField.Chebotarev
open NumberField NumberField.Chebotarev

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F]



variable {K F}

variable (K F) in
/-- **The continued `L`-series is the `L`-series on `Re s > 1`.** This holds for every Galois
extension `F / K` and every character `χ`, with no cyclotomic hypothesis. -/
@[simp]
theorem NumberField.Chebotarev.cyclotomicCharacterSeriesC_eq_LSeries (χ : (F ≃ₐ[K] F) →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    _root_.NumberField.Chebotarev.cyclotomicCharacterSeriesC K F χ s =
      _root_.LSeries (_root_.TauCeti.normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction) s := by
  rw [_root_.NumberField.Chebotarev.cyclotomicCharacterSeriesC]
  split_ifs with h
  exacts [h.choose_spec.2 s hs, _root_.rfl]



-- The continuation exists for a nontrivial ray class character: for `F = K(μ_m)` and a character
-- `χ` of `Gal(F/K)` with `χ ∘ cyclotomicArtin K F m` nontrivial, the `L`-series of the weight of
-- `χ` has a holomorphic continuation to `Re s > 1 - 1 / [K : ℚ]`.
private theorem NumberField.Chebotarev.exists_differentiableOn_eq_LSeries (m : ℕ) [_root_.NeZero m]
    [_root_.IsCyclotomicExtension {m} K F] (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (hχ : χ.comp (_root_.NumberField.Chebotarev.cyclotomicArtin K F m) ≠ 1) : ∃ f : ℂ → ℂ,
      _root_.DifferentiableOn ℂ f {s | 1 - 1 / (_root_.Module.finrank ℚ K : ℝ) < s.re} ∧ ∀ s : ℂ, 1 < s.re → f s =
        _root_.LSeries (_root_.TauCeti.normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction) s := by
  set S := (_root_.NumberField.Chebotarev.cyclotomicModulus K m).support
  set w := χ.galoisCharacterUnitaryWeight
  have hcorr : _root_.Differentiable ℂ
      fun s : ℂ ↦ ∏ 𝔭 ∈ S, (1 - w.1 𝔭.asIdeal / (_root_.Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s) :=
    _root_.Differentiable.fun_finsetProd fun 𝔭 _ ↦ (_root_.differentiable_const 1).sub
      ((_root_.differentiable_const _).div (differentiable_id.const_cpow (.inl 𝔭.natCast_absNorm_ne_zero))
        fun s ↦ by simp [_root_.Complex.cpow_eq_zero_iff, 𝔭.natCast_absNorm_ne_zero])
  -- On `Re s > 0` each local factor `1 - w(𝔭) N(𝔭) ^ (-s)` is nonzero, since `‖w(𝔭)‖ ≤ 1`.
  have hne {s : ℂ} (hs : 0 < s.re) :
      ∏ 𝔭 ∈ S, (1 - w.1 𝔭.asIdeal / (_root_.Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun 𝔭 _ ↦ (_root_.isUnit_one_sub_of_norm_lt_one <| by
      rw [_root_.norm_div, _root_.div_lt_one (zero_lt_one.trans (𝔭.one_lt_norm_absNorm_cpow hs))]
      exact (w.norm_le_one _).trans_lt (𝔭.one_lt_norm_absNorm_cpow hs)).ne_zero
  -- The continued `L`-function with the Euler factors at the primes dividing `m` deleted has
  -- cancellation; dividing by those factors, which are nonzero on `Re s > 0`, restores them.
  refine ⟨fun s ↦ _root_.TauCeti.continuedLFunctionOfWeight (w.restrict (S : _root_.Set _) S.finite_toSet) s /
      ∏ 𝔭 ∈ S, (1 - w.1 𝔭.asIdeal / (_root_.Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s), ?_, fun s hs ↦ ?_⟩
  · refine (_root_.TauCeti.differentiableOn_continuedLFunctionOfWeight
      (_root_.MonoidHom.hasCancellation_restrict_galoisCharacterUnitaryWeight χ hχ)).div
        hcorr.differentiableOn fun s hs ↦ hne ?_
    -- The half-plane `Re s > 1 - 1 / [K : ℚ]` lies in `Re s > 0`.
    exact (sub_nonneg.mpr <| _root_.div_le_one_of_le₀ (Nat.one_le_cast.mpr _root_.Module.finrank_pos)
      (_root_.Nat.cast_nonneg _)).trans_lt hs
  · dsimp only
    rw [_root_.TauCeti.continuedLFunctionOfWeight_restrict_of_one_lt_re w S hs,
      _root_.mul_div_cancel_right₀ _ (hne (by linarith)), _root_.TauCeti.continuedLFunctionOfWeight_eq_LSeries _ hs,
      _root_.TauCeti.UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
      _root_.MonoidHom.val_galoisCharacterUnitaryWeight]

variable (K F) in
/-- **Holomorphy on `Re s > 1 - 1 / [K : ℚ]`.** For `F = K(μ_m)` and a nontrivial character `χ` of
`Gal(F/K)`, the continued `L`-series of `χ` is holomorphic on the half-plane
`Re s > 1 - 1 / [K : ℚ]`. -/
theorem NumberField.Chebotarev.differentiableOn_cyclotomicCharacterSeriesC (m : ℕ) [_root_.NeZero m]
    [_root_.IsCyclotomicExtension {m} K F] (χ : (F ≃ₐ[K] F) →* ℂˣ) (hχ : χ ≠ 1) :
    _root_.DifferentiableOn ℂ (_root_.NumberField.Chebotarev.cyclotomicCharacterSeriesC K F χ)
      {s | 1 - 1 / (_root_.Module.finrank ℚ K : ℝ) < s.re} := by
  -- The Artin map is surjective, so `χ ∘ cyclotomicArtin K F m` is nontrivial.
  have h := _root_.NumberField.Chebotarev.exists_differentiableOn_eq_LSeries m χ <| by
    rwa [_root_.Ne, ← _root_.MonoidHom.one_comp (_root_.NumberField.Chebotarev.cyclotomicArtin K F m),
      _root_.MonoidHom.cancel_right (_root_.NumberField.Chebotarev.cyclotomicArtin_surjective K F m)]
  rw [_root_.NumberField.Chebotarev.cyclotomicCharacterSeriesC]
  split_ifs
  exact h.choose_spec.1

variable (K F) in
/-- **Analyticity at `s = 1`.** For `F = K(μ_m)` and a nontrivial character `χ` of `Gal(F/K)`,
the continued `L`-series of `χ` is analytic at `s = 1`, which lies in the half-plane of
`differentiableOn_cyclotomicCharacterSeriesC`. -/
theorem NumberField.Chebotarev.analyticAt_cyclotomicCharacterSeriesC_one (m : ℕ) [_root_.NeZero m] [_root_.IsCyclotomicExtension {m} K F]
    (χ : (F ≃ₐ[K] F) →* ℂˣ) (hχ : χ ≠ 1) : _root_.AnalyticAt ℂ (_root_.NumberField.Chebotarev.cyclotomicCharacterSeriesC K F χ) 1 :=
  (_root_.NumberField.Chebotarev.differentiableOn_cyclotomicCharacterSeriesC K F m χ hχ).analyticAt <|
    (_root_.isOpen_lt _root_.continuous_const _root_.Complex.continuous_re).mem_nhds
      (by simpa using _root_.TauCeti.cancellationExponent_lt_one (K := K))

-- As `s → 1⁺`, the prime sum over the primes of `K` that split completely in `F` tends to infinity.
private theorem NumberField.Chebotarev.tendsto_primeIdealZetaSum_frobeniusPrimeSet_one_atTop :
    _root_.Filter.Tendsto (fun σ : ℝ ↦ (_root_.NumberField.Chebotarev.frobeniusPrimeSet K F 1).primeIdealZetaSum σ) (𝓝[>] 1) _root_.Filter.atTop := by
  -- The completely split primes have positive density `1 / [F : K]`, and `log (1 / (σ - 1)) → ∞`.
  have hlog := _root_.Real.tendsto_log_one_div_sub_atTop 1
  exact (((_root_.NumberField.Set.hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one _ _).mp
    (_root_.NumberField.Chebotarev.hasDirichletDensity_frobeniusPrimeSet_one K F)).pos_mul_atTop (by simp [_root_.Module.finrank_pos])
      hlog).congr' <| (hlog.eventually_gt_atTop 0).mono fun σ hσ ↦ _root_.div_mul_cancel₀ _ hσ.ne'

-- At a completely split prime the Frobenius class is trivial, so its chosen representative is `1`.
private theorem NumberField.Chebotarev.artinSymbol_out_eq_one_of_mem_frobeniusPrimeSet_one {P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
    [P.asIdeal.IsMaximal]
    (hP : ∀ (Q : _root_.Ideal (𝓞 F)) [Q.IsPrime] [Q.LiesOver P.asIdeal], _root_.Algebra.IsUnramifiedAt (𝓞 K) Q)
    (h : P ∈ _root_.NumberField.Chebotarev.frobeniusPrimeSet K F 1) : (_root_.NumberField.artinSymbol P.asIdeal hP).out = 1 := by
  rw [← _root_.isConj_one_left, ← _root_.ConjClasses.mk_eq_mk_iff_isConj, ← _root_.ConjClasses.one_eq_mk_one,
    ← (_root_.NumberField.Chebotarev.mem_frobeniusPrimeSet_iff_artinSymbol_eq hP 1).mp h]
  exact _root_.Quotient.out_eq _

-- The character sum of a power of the Galois weights at a prime is a nonnegative real number, and
-- at a completely split prime the sum of the weights themselves is `#Gal(F/K)`.
private theorem NumberField.Chebotarev.exists_sum_galoisCharacterWeight_pow_eq [_root_.IsMulCommutative (F ≃ₐ[K] F)]
    (P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (j : ℕ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∑ ψ : (F ≃ₐ[K] F) →* ℂˣ, ψ.galoisCharacterWeight P.asIdeal ^ (j + 1) = r ∧
      (P ∈ _root_.NumberField.Chebotarev.frobeniusPrimeSet K F 1 → j = 0 → r = _root_.Nat.card (F ≃ₐ[K] F)) := by
  classical
  by_cases hP : P ∈ _root_.NumberField.Chebotarev.ramifiedPrimes K F
  · -- At a ramified prime every weight vanishes.
    refine ⟨0, _root_.le_rfl, ?_, fun h _ ↦ _root_.absurd (Finset.mem_coe.mpr hP)
      (_root_.NumberField.Chebotarev.frobeniusPrimeSet_subset_compl_ramifiedPrimes 1 h)⟩
    simp [(_root_.MonoidHom.galoisCharacterWeight_apply_eq_zero_iff _ P).mpr hP]
  · -- At an unramified prime, orthogonality evaluates the sum to `#Gal(F/K)` or `0`.
    rw [_root_.NumberField.Chebotarev.mem_ramifiedPrimes_iff, _root_.Classical.not_not] at hP
    have : P.asIdeal.IsMaximal := P.isMaximal
    refine ⟨if (_root_.NumberField.artinSymbol P.asIdeal hP).out ^ (j + 1) = 1 then _root_.Nat.card (F ≃ₐ[K] F) else 0,
      by positivity, by simpa [_root_.apply_ite] using
        _root_.AlgEquiv.sum_inv_mul_galoisCharacterWeight_pow_apply_of_unramified 1 P hP (j + 1),
      fun h1 hj ↦ ?_⟩
    simp [hj, _root_.NumberField.Chebotarev.artinSymbol_out_eq_one_of_mem_frobeniusPrimeSet_one hP h1]

-- For `σ > 1`, summing over the characters the Euler-product logarithm series of their `L`-series
-- gives the real series `∑_{P, e} r(P, e) / (N(P) ^ σ) ^ (e + 1) / (e + 1)`, where `r(P, e)` is
-- the character sum of the `(e + 1)`-th powers of the weights at `P`.
private theorem NumberField.Chebotarev.hasSum_sum_taylorSeries_galoisCharacterWeight {r : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ → ℝ}
    (hr : ∀ P j, ∑ ψ : (F ≃ₐ[K] F) →* ℂˣ, ψ.galoisCharacterWeight P.asIdeal ^ (j + 1) = r P j)
    {σ : ℝ} (hσ : 1 < σ) : _root_.HasSum (fun pe : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ ↦
      ((r pe.1 pe.2 / ((_root_.Ideal.absNorm pe.1.asIdeal : ℝ) ^ σ) ^ (pe.2 + 1) / (pe.2 + 1) : ℝ) : ℂ))
      (∑ ψ : (F ≃ₐ[K] F) →* ℂˣ, ∑' pe : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ,
        (ψ.galoisCharacterWeight pe.1.asIdeal / (_root_.Ideal.absNorm pe.1.asIdeal : ℂ) ^ (σ : ℂ)) ^
          (pe.2 + 1) / ((pe.2 : ℂ) + 1)) := by
  have hs (ψ : (F ≃ₐ[K] F) →* ℂˣ) :=
    ψ.summable_idealTerm_galoisCharacterWeight (K := K) (s := σ) (by simpa using hσ)
  refine (_root_.hasSum_sum fun (ψ : (F ≃ₐ[K] F) →* ℂˣ) _ ↦ (_root_.Complex.summable_taylorSeries_neg_log
    (ψ.galoisCharacterWeight.summable_div_of_summable_idealTerm (hs ψ))
    (ψ.galoisCharacterWeight.norm_div_lt_one_of_summable_idealTerm (hs ψ))).hasSum).congr_fun
    fun pe ↦ ?_
  simp [_root_.div_pow, ← _root_.Finset.sum_div, hr, _root_.Complex.ofReal_cpow]

-- For `F / K` abelian, the product over all characters `ψ` of `Gal(F/K)` of the `L`-series of
-- `galoisCharacterWeight ψ` tends to infinity in norm as `s → 1⁺` along the reals.
private theorem NumberField.Chebotarev.tendsto_norm_prod_LSeries_atTop [_root_.IsMulCommutative (F ≃ₐ[K] F)] :
    _root_.Filter.Tendsto (fun σ : ℝ ↦ ‖∏ ψ : (F ≃ₐ[K] F) →* ℂˣ,
      _root_.LSeries (_root_.TauCeti.normCoeff K ψ.galoisCharacterWeight.toIdealArithmeticFunction) σ‖)
      (𝓝[>] 1) _root_.Filter.atTop := by
  -- The Euler-product logarithms of all the `L`-series sum to a series of nonnegative reals,
  -- which dominates `#Gal(F/K)` times the prime sum over the completely split primes.
  choose r hr0 hr hrn using _root_.NumberField.Chebotarev.exists_sum_galoisCharacterWeight_pow_eq (K := K) (F := F)
  -- The real series `∑_{P, e} r(P, e) / (N(P) ^ σ) ^ (e + 1) / (e + 1)`.
  let ρ : ℝ → _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ → ℝ := fun σ pe ↦
    r pe.1 pe.2 / ((_root_.Ideal.absNorm pe.1.asIdeal : ℝ) ^ σ) ^ (pe.2 + 1) / (pe.2 + 1)
  have hρ0 (σ : ℝ) (pe) : 0 ≤ ρ σ pe := by
    have := hr0 pe.1 pe.2
    positivity
  refine _root_.Filter.tendsto_atTop_mono' _ ?_
    ((_root_.NumberField.Chebotarev.tendsto_primeIdealZetaSum_frobeniusPrimeSet_one_atTop (K := K) (F := F)).const_mul_atTop
      (Nat.cast_pos.mpr _root_.Nat.card_pos : (0 : ℝ) < _root_.Nat.card (F ≃ₐ[K] F)))
  filter_upwards [_root_.self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  have hsum := _root_.NumberField.Chebotarev.hasSum_sum_taylorSeries_galoisCharacterWeight hr hσ
  -- The product of the `L`-series is the exponential of the real series.
  rw [← _root_.Finset.prod_congr _root_.rfl fun ψ _ ↦ _root_.TauCeti.MultiplicativeIdealWeight.exp_tsum_prime_pow_eq_LSeries _
      (ψ.summable_idealTerm_galoisCharacterWeight (K := K) (s := σ)
        (by simpa using hσ)),
    ← _root_.Complex.exp_sum, ← hsum.tsum_eq, ← _root_.Complex.ofReal_tsum, _root_.Complex.norm_exp_ofReal,
    _root_.NumberField.Set.primeIdealZetaSum_def, ← _root_.tsum_mul_left]
  refine _root_.le_trans ?_ ((_root_.le_add_of_nonneg_right _root_.zero_le_one).trans (_root_.Real.add_one_le_exp _))
  refine _root_.le_of_eq_of_le (_root_.tsum_congr fun P ↦ ?_) (_root_.tsum_comp_le_tsum_of_inj
    (Complex.summable_ofReal.mp hsum.summable) (hρ0 σ)
    (i := fun P : _root_.NumberField.Chebotarev.frobeniusPrimeSet K F 1 ↦ (P.1, 0)) fun P Q h ↦ _root_.Subtype.ext (_root_.congrArg _root_.Prod.fst h))
  simp [hrn P.1 0 P.2 _root_.rfl, _root_.Real.rpow_neg, _root_.div_eq_mul_inv]

open scoped Classical in
-- If the continued `L`-series of `χ ≠ 1` vanishes at `1`, then as `σ → 1⁺` the `L`-series of every
-- character converges after renormalising: that of the trivial character multiplied by `σ - 1`,
-- that of `χ` divided by `σ - 1`, and the others unchanged.
private theorem NumberField.Chebotarev.exists_tendsto_mulSingle_mul_LSeries (m : ℕ) [_root_.NeZero m]
    [_root_.IsCyclotomicExtension {m} K F] {χ : (F ≃ₐ[K] F) →* ℂˣ} (hχ : χ ≠ 1)
    (h0 : _root_.NumberField.Chebotarev.cyclotomicCharacterSeriesC K F χ 1 = 0) (ψ : (F ≃ₐ[K] F) →* ℂˣ) :
    ∃ z, _root_.Filter.Tendsto (fun σ : ℝ ↦ _root_.Pi.mulSingle (M := fun _ ↦ ℂ) 1 ((σ : ℂ) - 1) ψ *
      _root_.Pi.mulSingle (M := fun _ ↦ ℂ) χ ((σ : ℂ) - 1)⁻¹ ψ *
        _root_.LSeries (_root_.TauCeti.normCoeff K ψ.galoisCharacterWeight.toIdealArithmeticFunction) σ) (𝓝[>] 1)
      (𝓝 z) := by
  have hray : _root_.Filter.Tendsto (fun σ : ℝ ↦ (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) :=
    _root_.Complex.ofReal_one ▸ Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
      fun σ (hσ : 1 < σ) ↦ Complex.ofReal_injective.ne hσ.ne'
  have hL : ∀ᶠ σ : ℝ in 𝓝[>] 1, _root_.NumberField.Chebotarev.cyclotomicCharacterSeriesC K F ψ σ =
      _root_.LSeries (_root_.TauCeti.normCoeff K ψ.galoisCharacterWeight.toIdealArithmeticFunction) σ :=
    _root_.eventually_nhdsWithin_of_forall fun σ (hσ : 1 < σ) ↦
      _root_.NumberField.Chebotarev.cyclotomicCharacterSeriesC_eq_LSeries K F ψ (by simpa using hσ)
  by_cases h1 : ψ = 1
  · -- The trivial character's `L`-series has a simple pole at `1`.
    subst h1
    exact ⟨_, (_root_.TauCeti.tendsto_sub_one_mul_LSeries_ofBadPrimes (_root_.NumberField.Chebotarev.ramifiedPrimes K F)).congr fun σ ↦ by
      simp [_root_.Ne.symm hχ]⟩
  have hana := _root_.NumberField.Chebotarev.analyticAt_cyclotomicCharacterSeriesC_one K F m ψ h1
  by_cases h2 : ψ = χ
  · -- The series of `χ` vanishes at `1`, so dividing by `σ - 1` gives a difference quotient.
    subst h2
    refine ⟨_, ((hasDerivAt_iff_tendsto_slope.mp hana.differentiableAt.hasDerivAt).comp
      hray).congr' ?_⟩
    filter_upwards [hL] with σ hσ
    simp [_root_.slope_def_field, h0, hσ, h1, _root_.div_eq_inv_mul]
  · -- Any other series is continuous at `1`.
    refine ⟨_, (hana.continuousAt.tendsto.comp (hray.mono_right _root_.nhdsWithin_le_nhds)).congr' ?_⟩
    filter_upwards [hL] with σ hσ
    simp [h1, h2, hσ]

variable (K F) in
/-- **Nonvanishing at `s = 1`.** For `F = K(μ_m)` and a nontrivial character `χ` of `Gal(F/K)`,
the continued `L`-series of `χ` does not vanish at `s = 1`. -/
theorem solution (m : ℕ) [_root_.NeZero m] [_root_.IsCyclotomicExtension {m} K F]
    (χ : (F ≃ₐ[K] F) →* ℂˣ) (hχ : χ ≠ 1) : _root_.NumberField.Chebotarev.cyclotomicCharacterSeriesC K F χ 1 ≠ 0 := by
  intro h0
  have := _root_.IsCyclotomicExtension.isMulCommutative {m} K F
  -- The product of all the `L`-series is unbounded as `σ → 1⁺`. But the trivial character's
  -- series times `σ - 1` converges, the series of `χ` divided by `σ - 1` converges since it
  -- vanishes at `1`, and the other series converge, so the product converges.
  choose z hz using _root_.NumberField.Chebotarev.exists_tendsto_mulSingle_mul_LSeries m hχ h0
  refine _root_.not_tendsto_atTop_of_tendsto_nhds (_root_.tendsto_finsetProd _root_.Finset.univ fun ψ _ ↦ hz ψ).norm
    ((_root_.NumberField.Chebotarev.tendsto_norm_prod_LSeries_atTop (K := K) (F := F)).congr' ?_)
  filter_upwards [_root_.self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  -- The renormalising factors multiply to `(σ - 1) * (σ - 1)⁻¹ = 1`.
  have hσ1 : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (Complex.ofReal_injective.ne hσ.ne')
  simp [_root_.Finset.prod_mul_distrib, _root_.Finset.prod_pi_mulSingle', hσ1]

end NumberField.Chebotarev

end
end
