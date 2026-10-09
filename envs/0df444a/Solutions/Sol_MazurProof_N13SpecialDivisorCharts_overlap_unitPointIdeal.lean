-- Prove2me | solution 1 for MazurProof.N13SpecialDivisorCharts.overlap_unitPointIdeal
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T06:46:07.406852+00:00
-- url     : https://prove2.me/submissions/5a4efbc6-2ffa-4a81-9a0e-13c657b96887

import Mathlib
import Definitions.Def_MazurN13_L3

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13SpecialDivisorCharts =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialDivisorCharts =====
section
/-!
# Canonical special-chart ideals of degree-two divisors

The completed special N13 curve is covered by its ordinary affine chart and
its infinity chart.  A finite point with horizontal coordinate zero is absent
from the overlap, a finite point with horizontal coordinate one lies on both
charts, and an infinity point is absent from the ordinary affine chart.

This file assigns to every completed point its compatible pair of chart
ideals.  Products of two point pairs then descend through the symmetric square
to give canonical chart ideals for every effective divisor of degree two.
-/
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialDivisorCharts
noncomputable section
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT
/-- On the overlap, the point ideals written in the coordinates
`x=t⁻¹` and `y=x³v` agree at `x=t=1`.

The first generators differ by the units `x` and `t`.  Once those generators
are identified, the difference between the second generators is a multiple
of `x³-1` or `t³-1`, respectively. -/
theorem overlap_unitPointIdeal
    (c : SpecialOverlap) :
    Ideal.span
        {N13SpecialCurveOverlap.xOverlap - 1,
          N13SpecialCurveOverlap.xOverlap ^ 3 *
              N13SpecialCurveOverlap.vOverlap - c} =
      Ideal.span
        {N13SpecialCurveOverlap.tOverlap - 1,
          N13SpecialCurveOverlap.vOverlap - c} := by
  let x := N13SpecialCurveOverlap.xOverlap
  let t := N13SpecialCurveOverlap.tOverlap
  let v := N13SpecialCurveOverlap.vOverlap
  let I : Ideal SpecialOverlap :=
    Ideal.span {x - 1, x ^ 3 * v - c}
  let J : Ideal SpecialOverlap :=
    Ideal.span {t - 1, v - c}
  change I = J
  have htx : t * x = 1 :=
    N13SpecialCurveOverlap.tOverlap_mul_xOverlap
  have hxI : x - 1 ∈ I :=
    Ideal.subset_span (by simp)
  have hxyI : x ^ 3 * v - c ∈ I :=
    Ideal.subset_span (by simp)
  have htJ : t - 1 ∈ J :=
    Ideal.subset_span (by simp)
  have hvJ : v - c ∈ J :=
    Ideal.subset_span (by simp)
  have hxJ : x - 1 ∈ J := by
    have hmem := Ideal.mul_mem_left J (-x) htJ
    convert hmem using 1
    linear_combination htx
  have hx3J : x ^ 3 - 1 ∈ J := by
    have hmem :=
      Ideal.mul_mem_left J (x ^ 2 + x + 1) hxJ
    convert hmem using 1
    ring
  have hxyJ : x ^ 3 * v - c ∈ J := by
    have h₁ := Ideal.mul_mem_left J (x ^ 3) hvJ
    have h₂ := Ideal.mul_mem_left J c hx3J
    have hmem := Ideal.add_mem J h₁ h₂
    convert hmem using 1
    ring
  have htI : t - 1 ∈ I := by
    have hmem := Ideal.mul_mem_left I (-t) hxI
    convert hmem using 1
    linear_combination htx
  have ht3I : t ^ 3 - 1 ∈ I := by
    have hmem :=
      Ideal.mul_mem_left I (t ^ 2 + t + 1) htI
    convert hmem using 1
    ring
  have hvI : v - c ∈ I := by
    have h₁ := Ideal.mul_mem_left I (t ^ 3) hxyI
    have h₂ := Ideal.mul_mem_left I c ht3I
    have hmem := Ideal.add_mem I h₁ h₂
    have htx3 : t ^ 3 * x ^ 3 = 1 := by
      calc
        t ^ 3 * x ^ 3 = (t * x) ^ 3 := by ring
        _ = 1 := by rw [htx, one_pow]
    have heq :
        t ^ 3 * (x ^ 3 * v - c) + c * (t ^ 3 - 1) =
          v - c := by
      calc
        _ = (t ^ 3 * x ^ 3) * v - c := by ring
        _ = v - c := by rw [htx3, one_mul]
    rw [heq] at hmem
    exact hmem
  apply le_antisymm
  · exact Ideal.span_le.mpr (by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hxJ
      · exact hxyJ)
  · exact Ideal.span_le.mpr (by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact htI
      · exact hvI)
end
end MazurProof.N13SpecialDivisorCharts
end

end

theorem solution : type_of% @MazurProof.N13SpecialDivisorCharts.overlap_unitPointIdeal := @MazurProof.N13SpecialDivisorCharts.overlap_unitPointIdeal
