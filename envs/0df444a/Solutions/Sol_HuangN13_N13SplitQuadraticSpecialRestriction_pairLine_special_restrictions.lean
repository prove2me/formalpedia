-- Prove2me | solution 1 for HuangN13.N13SplitQuadraticSpecialRestriction.pairLine_special_restrictions
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:19:58.395502+00:00
-- url     : https://prove2.me/submissions/e84bbdd4-8a34-4392-9661-4902a21314aa

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_FiniteInfinityClosureCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Theorems.Thm_MazurProof_N13InfinityLineSpecialRestriction_map_pointIdeal
import Theorems.Thm_MazurProof_N13SpecialDivisorCharts_map_infinityPointIdeal
import Theorems.Thm_MazurProof_N13SpecialDivisorCharts_overlap_unitPointIdeal

set_option autoImplicit false

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem reduce_integralBaseClass (p : IntegralBase) :
    reduceCoordinate (integralBaseClass p) =
      specialBaseClass (reducePoly p) := by
  exact AdjoinRoot.map_of
    reducePoly
    N13IntegralInfinityChart.infinityCurvePoly
    N13SpecialInfinityChart.curvePoly
    special_curve_dvd p
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoChartSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Chartwise restriction carries tensor products of proper lines to products
of their reduced affine ideals. -/
@[simp] theorem restrict_tensor_affineIdeal
    (L M : Line) :
    (restrict (N13TwoChartLineTensor.tensor L M)).affineIdeal =
      (restrict L).affineIdeal * (restrict M).affineIdeal := by
  exact Ideal.map_mul _ _ _
end
end MazurProof.N13TwoChartSpecialRestriction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoChartSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Chartwise restriction carries tensor products of proper lines to products
of their reduced infinity ideals. -/
@[simp] theorem restrict_tensor_infinityIdeal
    (L M : Line) :
    (restrict (N13TwoChartLineTensor.tensor L M)).infinityIdeal =
      (restrict L).infinityIdeal * (restrict M).infinityIdeal := by
  exact Ideal.map_mul _ _ _
end
end MazurProof.N13TwoChartSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialDivisorCharts
noncomputable section
@[simp] theorem ofDivisor_mk (P Q : CurvePoint) :
    ofDivisor s(P, Q) =
      tensor (point P) (point Q) :=
  rfl
end
end MazurProof.N13SpecialDivisorCharts
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13EscapingPointSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13EscapingPointSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- The reduced affine-chart ideal of an escaping point line is the unit
ideal because its horizontal generator `1-t₀x` reduces to `1`. -/
theorem restrict_nonintegralPointLine_affineIdeal
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    (N13TwoChartSpecialRestriction.restrict
      (N13IntegralInfinityPointSpread.nonintegralPointLine
        x y hx hxy)).affineIdeal =
      (N13SpecialDivisorCharts.point
        (N13ProperCurveReduction.reduceNonintegralAffine
          x y hx hxy)).affineIdeal := by
  let P : N13IntegralInfinityPointSpread.IntegralInfinityPoint :=
    N13ProperCurveReduction.nonintegralInfinityLift x y hx hxy
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralInfinityPointSpread.affinePointIdeal P) =
      ⊤
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (N13IntegralInfinityPointSpread.affineU P)
          (N13IntegralInfinityPointSpread.affineV P)) =
      ⊤
  rw [N13GeneralizedMumfordReduction.map_mumfordIdeal]
  have ht :
      N13GeneralizedMumfordReduction.reduceBase P.1.1 = 0 := by
    exact
      N13IntegralInfinityPointSpread.nonintegralLift_t_residue_eq_zero
        x y hx hxy
  have hu :
      N13GeneralizedMumfordReduction.reducePoly
        (N13IntegralInfinityPointSpread.affineU P) = 1 := by
    simp [N13IntegralInfinityPointSpread.affineU,
      N13GeneralizedMumfordReduction.reducePoly_apply, ht]
  rw [hu, Ideal.eq_top_iff_one]
  exact
    N13GoodCoordinateRingTwo.xClass_mem_mumfordIdeal
      1
      (N13GeneralizedMumfordReduction.reducePoly
        (N13IntegralInfinityPointSpread.affineV P))
end
end MazurProof.N13EscapingPointSpecialRestriction
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13EscapingPointSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13EscapingPointSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- The reduced infinity-chart ideal is exactly the canonical ideal of the
properly reduced point at infinity. -/
theorem restrict_nonintegralPointLine_infinityIdeal
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    (N13TwoChartSpecialRestriction.restrict
      (N13IntegralInfinityPointSpread.nonintegralPointLine
        x y hx hxy)).infinityIdeal =
      (N13SpecialDivisorCharts.point
        (N13ProperCurveReduction.reduceNonintegralAffine
          x y hx hxy)).infinityIdeal := by
  let P : N13IntegralInfinityPointSpread.IntegralInfinityPoint :=
    N13ProperCurveReduction.nonintegralInfinityLift x y hx hxy
  change
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (N13IntegralInfinityPointSpread.pointIdeal P) =
      N13SpecialDivisorCharts.infinityPointIdeal
        0
        (N13IntegralInfinityReduction.reduceBase P.1.2)
  rw [N13InfinityLineSpecialRestriction.map_pointIdeal]
  congr 2
  exact
    N13IntegralInfinityPointSpread.nonintegralLift_t_residue_eq_zero
      x y hx hxy
end
end MazurProof.N13EscapingPointSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralAffinePointSpecialClass
noncomputable section
/-- The two-adic coefficient ring of the integral point graph. -/
abbrev R₂ : Type :=
  N13GeneralizedMumfordReduction.R₂
end
end MazurProof.N13IntegralAffinePointSpecialClass
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralAffinePointSpecialClass
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralAffinePointSpecialClass.instFactPrimeOfNatNat_fLT
/-- The literal linear graph ideal of the reduced affine point. -/
def reducedPointIdeal (P : IntegralPoint) : Ideal SpecialRing :=
  N13GoodCoordinateRingTwo.mumfordIdeal
    (X - C (PadicInt.toZMod P.1.1))
    (C (PadicInt.toZMod P.1.2))
end
end MazurProof.N13IntegralAffinePointSpecialClass
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralAffinePointSpecialClass
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralAffinePointSpecialClass.instFactPrimeOfNatNat_fLT
/-- Reduction of the integral affine point ideal is exactly the linear
Mumford graph of the coefficientwise reduced point.

This is an equality of ideals after base change, rather than only a
containment or a comparison of quotient cardinalities. -/
theorem map_pointIdeal_eq_reducedPointIdeal
    (P : IntegralPoint) :
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralAffinePointSpread.pointIdeal P) =
      reducedPointIdeal P := by
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂)
          (N13IntegralAffinePointSpread.pointU P)
          (N13IntegralAffinePointSpread.pointV P)) =
      reducedPointIdeal P
  rw [N13GeneralizedMumfordReduction.map_mumfordIdeal]
  simp [reducedPointIdeal,
    N13IntegralAffinePointSpread.pointU,
    N13IntegralAffinePointSpread.pointV,
    N13GeneralizedMumfordReduction.reducePoly_apply,
    N13GeneralizedMumfordReduction.reduceBase]
end
end MazurProof.N13IntegralAffinePointSpecialClass
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralAffinePointSpecialClass
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The affine component of the proper integral point line has the same exact
special graph as the stored integral point.

The contracted infinity ideal supplies proper gluing but does not alter this
affine reduction equality. -/
theorem map_integralPointTwoChartLine_affineIdeal
    (P : IntegralPoint) :
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P).affineIdeal =
      reducedPointIdeal P := by
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralAffinePointSpread.pointIdeal P) =
      reducedPointIdeal P
  exact map_pointIdeal_eq_reducedPointIdeal P
end
end MazurProof.N13IntegralAffinePointSpecialClass
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- An ideal containing `1-t a` is already saturated with respect to powers
of `t`.

Indeed, if `tⁿz` belongs to the ideal, multiplication by `aⁿ` recovers `z`
modulo the ideal because `(ta)ⁿ=1` there. -/
theorem under_map_eq_of_one_sub_t_mul_mem
    (J : Ideal InfinityCurve)
    (a : InfinityCurve)
    (hunit :
      1 - N13IntegralInfinityChart.tClass * a ∈ J) :
    (Ideal.map
      (algebraMap InfinityCurve InfinityOverlap) J).under
        InfinityCurve =
      J := by
  apply le_antisymm
  · intro z hz
    change
      algebraMap InfinityCurve InfinityOverlap z ∈
        Ideal.map (algebraMap InfinityCurve InfinityOverlap) J at hz
    obtain ⟨m, hm, hmz⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff
        (Submonoid.powers N13IntegralInfinityChart.tClass)
        InfinityOverlap J z).mp hz
    obtain ⟨n, hn⟩ :=
      (Submonoid.mem_powers_iff
        m N13IntegralInfinityChart.tClass).mp hm
    rw [← hn] at hmz
    have hpow_all :
        ∀ k : ℕ,
          1 - (N13IntegralInfinityChart.tClass * a) ^ k ∈ J := by
      intro k
      induction k with
      | zero =>
          simp
      | succ k ih =>
          have hmul :=
            Ideal.mul_mem_left J
              ((N13IntegralInfinityChart.tClass * a) ^ k)
              hunit
          have hadd := Ideal.add_mem J ih hmul
          convert hadd using 1
          ring
    have hpow :=
      hpow_all n
    have hmultiple :=
      Ideal.mul_mem_left J (a ^ n) hmz
    have hcorrection :=
      Ideal.mul_mem_left J z hpow
    have hadd := Ideal.add_mem J hmultiple hcorrection
    convert hadd using 1
    ring
  · exact Ideal.le_comap_map
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Weighted infinity-chart ideal of an integral affine point. -/
def weightedInfinityIdeal (P : IntegralPoint) : Ideal InfinityCurve :=
  Ideal.span
    {1 -
        N13IntegralInfinityReduction.integralBaseClass (C P.1.1) *
          N13IntegralInfinityChart.tClass,
      N13IntegralInfinityChart.vClass -
        N13IntegralInfinityReduction.integralBaseClass (C P.1.2) *
          N13IntegralInfinityChart.tClass ^ 3}
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
/-- Multiplying two generators by units does not change the ideal they
generate. -/
private theorem span_pair_unit_mul
    {A : Type*} [CommRing A]
    (u v : Aˣ) (a b : A) :
    Ideal.span ({(u : A) * a, (v : A) * b} : Set A) =
      Ideal.span ({a, b} : Set A) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      have hmem :
          ((u⁻¹ : Aˣ) : A) * ((u : A) * a) ∈
            Ideal.span ({(u : A) * a, (v : A) * b} : Set A) :=
        Ideal.mul_mem_left _ _
          (Ideal.subset_span (by simp))
      simpa [mul_assoc] using hmem
    · rw [hz]
      have hmem :
          ((v⁻¹ : Aˣ) : A) * ((v : A) * b) ∈
            Ideal.span ({(u : A) * a, (v : A) * b} : Set A) :=
        Ideal.mul_mem_left _ _
          (Ideal.subset_span (by simp))
      simpa [mul_assoc] using hmem
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The weighted infinity ideal and the affine point ideal have the same
extension to the ordinary overlap. -/
theorem map_weightedInfinityIdeal (P : IntegralPoint) :
    Ideal.map
        (algebraMap InfinityCurve InfinityOverlap)
        (weightedInfinityIdeal P) =
      Ideal.map
        N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (N13IntegralAffinePointSpread.pointIdeal P) := by
  simp [weightedInfinityIdeal,
    N13IntegralAffinePointSpread.pointIdeal,
    N13IntegralAffinePointSpread.integralSemiGraph,
    N13IntegralAffinePointSpread.pointU,
    N13IntegralAffinePointSpread.pointV,
    N13GeneralizedMumfordIntegral.mumfordIdeal,
    N13GeneralizedMumfordIntegral.ySubClass,
    Ideal.map_span, Set.image_pair,
    N13IntegralInfinityReduction.integralBaseClass,
    N13GeneralizedMumfordIntegral.xClass,
    N13GeneralizedMumfordIntegral.mk,
    N13OrdinaryCurveOverlap.affineYImage,
    N13OrdinaryCurveOverlap.affineCoeffMap,
    N13OrdinaryCurveOverlap.coefficientToInfinityOverlap]
  change
    Ideal.span
        {1 -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1 *
              N13OrdinaryCurveOverlap.tOverlap,
          N13OrdinaryCurveOverlap.vOverlap -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 *
              N13OrdinaryCurveOverlap.tOverlap ^ 3} =
      Ideal.span
        {N13OrdinaryCurveOverlap.xOverlap -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1,
          N13OrdinaryCurveOverlap.xOverlap ^ 3 *
              N13OrdinaryCurveOverlap.vOverlap -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2}
  let ux : InfinityOverlapˣ :=
    N13OrdinaryCurveOverlap.xOverlap_isUnit.unit
  have hux :
      (ux : InfinityOverlap) =
        N13OrdinaryCurveOverlap.xOverlap :=
    N13OrdinaryCurveOverlap.xOverlap_isUnit.unit_spec
  have hfirst :
      N13OrdinaryCurveOverlap.xOverlap -
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1 =
        (ux : InfinityOverlap) *
          (1 -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1 *
              N13OrdinaryCurveOverlap.tOverlap) := by
    rw [hux]
    linear_combination
      N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1 *
        N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap
  have hsecond :
      N13OrdinaryCurveOverlap.xOverlap ^ 3 *
            N13OrdinaryCurveOverlap.vOverlap -
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 =
        ((ux ^ 3 : InfinityOverlapˣ) : InfinityOverlap) *
          (N13OrdinaryCurveOverlap.vOverlap -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 *
              N13OrdinaryCurveOverlap.tOverlap ^ 3) := by
    change
      N13OrdinaryCurveOverlap.xOverlap ^ 3 *
            N13OrdinaryCurveOverlap.vOverlap -
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 =
        (ux : InfinityOverlap) ^ 3 *
          (N13OrdinaryCurveOverlap.vOverlap -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 *
              N13OrdinaryCurveOverlap.tOverlap ^ 3)
    rw [hux]
    linear_combination
      N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 *
        (N13OrdinaryCurveOverlap.xOverlap ^ 2 *
        N13OrdinaryCurveOverlap.tOverlap ^ 2 +
        N13OrdinaryCurveOverlap.xOverlap *
          N13OrdinaryCurveOverlap.tOverlap +
        1) *
        N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap
  rw [hfirst, hsecond]
  exact
    (span_pair_unit_mul
      ux (ux ^ 3)
      (1 -
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1 *
          N13OrdinaryCurveOverlap.tOverlap)
      (N13OrdinaryCurveOverlap.vOverlap -
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 *
          N13OrdinaryCurveOverlap.tOverlap ^ 3)).symm
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The horizontal weighted equation explicitly makes `t` invertible modulo
the weighted ideal. -/
theorem one_sub_t_mul_mem_weightedInfinityIdeal
    (P : IntegralPoint) :
    1 -
        N13IntegralInfinityChart.tClass *
          N13IntegralInfinityReduction.integralBaseClass (C P.1.1) ∈
      weightedInfinityIdeal P := by
  have hgen :
      1 -
          N13IntegralInfinityReduction.integralBaseClass (C P.1.1) *
            N13IntegralInfinityChart.tClass ∈
        weightedInfinityIdeal P :=
    Ideal.subset_span (by simp)
  simpa [mul_comm] using hgen
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The weighted point ideal has no additional component supported at
`t=0`; extending to the overlap and contracting returns it unchanged. -/
theorem under_map_weightedInfinityIdeal
    (P : IntegralPoint) :
    (Ideal.map
      (algebraMap InfinityCurve InfinityOverlap)
      (weightedInfinityIdeal P)).under InfinityCurve =
        weightedInfinityIdeal P :=
  under_map_eq_of_one_sub_t_mul_mem
    (weightedInfinityIdeal P)
    (N13IntegralInfinityReduction.integralBaseClass (C P.1.1))
    (one_sub_t_mul_mem_weightedInfinityIdeal P)
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The abstract contracted infinity closure of a finite affine point is
exactly its explicit weighted infinity ideal. -/
theorem infinityClosure_pointIdeal
    (P : IntegralPoint) :
    N13FiniteAffineTwoChart.infinityClosure
        (N13IntegralAffinePointSpread.pointIdeal P) =
      weightedInfinityIdeal P := by
  rw [N13FiniteAffineTwoChart.infinityClosure,
    ← map_weightedInfinityIdeal P]
  exact under_map_weightedInfinityIdeal P
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Reduction of the integral weighted ideal is exactly the weighted ideal
with reduced coordinates. -/
theorem map_weightedInfinityIdeal_reduce
    (P : IntegralPoint) :
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (weightedInfinityIdeal P) =
      reducedWeightedInfinityIdeal P := by
  simp [weightedInfinityIdeal, reducedWeightedInfinityIdeal,
    Ideal.map_span, Set.image_pair,
    N13IntegralInfinityReduction.reduce_integralBaseClass,
    N13IntegralInfinityReduction.reducePoly,
    N13IntegralInfinityReduction.reduceBase,
    N13IntegralInfinityReduction.specialBaseClass]
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13FiniteAffinePointInfinityClosure.instFactPrimeOfNatNat_fLT
/-- At the unit horizontal coordinate, the weighted point equations
`(1-t, v-bt³)` generate the same ideal as the ordinary point equations
`(t-1, v-b)`. -/
theorem reducedWeightedUnit_eq_infinityPointIdeal
    (b : N13GoodModelTwo.F2) :
    Ideal.span
        {1 - N13SpecialInfinityChart.tClass,
          N13SpecialInfinityChart.vClass -
            N13IntegralInfinityReduction.specialBaseClass (C b) *
              N13SpecialInfinityChart.tClass ^ 3} =
      N13SpecialDivisorCharts.infinityPointIdeal 1 b := by
  let t := N13SpecialInfinityChart.tClass
  let v := N13SpecialInfinityChart.vClass
  let c :=
    N13IntegralInfinityReduction.specialBaseClass (C b)
  let I : Ideal N13IntegralInfinityReduction.SpecialRing :=
    Ideal.span {1 - t, v - c * t ^ 3}
  let J : Ideal N13IntegralInfinityReduction.SpecialRing :=
    Ideal.span {t - 1, v - c}
  change I = J
  have honeI : 1 - t ∈ I :=
    Ideal.subset_span (by simp)
  have hvI : v - c * t ^ 3 ∈ I :=
    Ideal.subset_span (by simp)
  have htJ : t - 1 ∈ J :=
    Ideal.subset_span (by simp)
  have hvJ : v - c ∈ J :=
    Ideal.subset_span (by simp)
  have htI : t - 1 ∈ I := by
    have hmem := Ideal.mul_mem_left I (-1) honeI
    convert hmem using 1
    ring
  have honeJ : 1 - t ∈ J := by
    have hmem := Ideal.mul_mem_left J (-1) htJ
    convert hmem using 1
    ring
  have ht3I : t ^ 3 - 1 ∈ I := by
    have hmem :=
      Ideal.mul_mem_left I (t ^ 2 + t + 1) htI
    convert hmem using 1
    ring
  have hone3J : 1 - t ^ 3 ∈ J := by
    have hmem :=
      Ideal.mul_mem_left J (t ^ 2 + t + 1) honeJ
    convert hmem using 1
    ring
  have hvPlainI : v - c ∈ I := by
    have h₁ := hvI
    have h₂ := Ideal.mul_mem_left I c ht3I
    have hmem := Ideal.add_mem I h₁ h₂
    convert hmem using 1
    ring
  have hvWeightedJ : v - c * t ^ 3 ∈ J := by
    have h₁ := hvJ
    have h₂ := Ideal.mul_mem_left J c hone3J
    have hmem := Ideal.add_mem J h₁ h₂
    convert hmem using 1
    ring
  have hIJ : I = J := by
    apply le_antisymm
    · exact Ideal.span_le.mpr (by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact honeJ
        · exact hvWeightedJ)
    · exact Ideal.span_le.mpr (by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact htI
        · exact hvPlainI)
  rw [hIJ]
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13FiniteAffinePointInfinityClosure.instFactPrimeOfNatNat_fLT
/-- If the affine horizontal coordinate reduces to zero, the weighted
infinity ideal reduces to the unit ideal, as the point is absent from that
chart. -/
theorem reducedWeightedInfinityIdeal_eq_top
    (P : IntegralPoint)
    (ha :
      N13GeneralizedMumfordReduction.reduceBase P.1.1 = 0) :
    reducedWeightedInfinityIdeal P = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hgen :
      1 -
          N13IntegralInfinityReduction.specialBaseClass
              (C (N13GeneralizedMumfordReduction.reduceBase P.1.1)) *
            N13SpecialInfinityChart.tClass ∈
        reducedWeightedInfinityIdeal P :=
    Ideal.subset_span (by simp)
  simpa [ha, N13IntegralInfinityReduction.specialBaseClass] using hgen
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralAffinePointSpecialClass.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13FiniteAffinePointInfinityClosure.instFactPrimeOfNatNat_fLT
/-- The infinity component of an integral affine point line reduces exactly
to the canonical infinity-chart ideal of its reduced special point. -/
theorem map_infinityClosure_pointIdeal
    (P : IntegralPoint) :
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (N13FiniteAffineTwoChart.infinityClosure
          (N13IntegralAffinePointSpread.pointIdeal P)) =
      (N13SpecialDivisorCharts.point
        (N13IntegralAffinePointSpecialClass.reducedPoint P)).infinityIdeal := by
  rw [infinityClosure_pointIdeal, map_weightedInfinityIdeal_reduce]
  let a :=
    N13GeneralizedMumfordReduction.reduceBase P.1.1
  let b :=
    N13GeneralizedMumfordReduction.reduceBase P.1.2
  have ha : a = 0 ∨ a = 1 :=
    N13GoodModelTwo.fixedTwo_eq_zero_or_one
      a (ZMod.pow_card a)
  rcases ha with ha | ha
  · rw [reducedWeightedInfinityIdeal_eq_top P ha]
    have ha0 :
        PadicInt.toZMod P.1.1 = 0 := by
      exact ha
    simp [N13IntegralAffinePointSpecialClass.reducedPoint,
      N13SpecialDivisorCharts.point,
      N13SpecialDivisorCharts.affineZeroPoint, ha0]
  · have hweighted :
        reducedWeightedInfinityIdeal P =
          N13SpecialDivisorCharts.infinityPointIdeal 1 b := by
      simpa [reducedWeightedInfinityIdeal, a, b, ha,
        N13IntegralInfinityReduction.specialBaseClass] using
        reducedWeightedUnit_eq_infinityPointIdeal b
    rw [hweighted]
    have hb :
        b = PadicInt.toZMod P.1.2 := by
      rfl
    rw [hb]
    have ha1 :
        PadicInt.toZMod P.1.1 = 1 := by
      exact ha
    have ha0 :
        PadicInt.toZMod P.1.1 ≠ 0 := by
      rw [ha1]
      norm_num
    simp [N13IntegralAffinePointSpecialClass.reducedPoint,
      N13SpecialDivisorCharts.point,
      N13SpecialDivisorCharts.affineOnePoint, ha0]
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralAffinePointSpecialClass.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13FiniteAffinePointInfinityClosure.instFactPrimeOfNatNat_fLT
/-- The affine component of the integral point line reduces to the canonical
affine ideal of the same reduced point. -/
theorem restrict_integralPointTwoChartLine_affineIdeal
    (P : IntegralPoint) :
    (N13TwoChartSpecialRestriction.restrict
      (N13FiniteAffineTwoChart.integralPointTwoChartLine P)).affineIdeal =
      (N13SpecialDivisorCharts.point
        (N13IntegralAffinePointSpecialClass.reducedPoint P)).affineIdeal := by
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P).affineIdeal =
      _
  rw [
    N13IntegralAffinePointSpecialClass.map_integralPointTwoChartLine_affineIdeal]
  let a :=
    N13GeneralizedMumfordReduction.reduceBase P.1.1
  have ha : a = 0 ∨ a = 1 :=
    N13GoodModelTwo.fixedTwo_eq_zero_or_one
      a (ZMod.pow_card a)
  rcases ha with ha | ha
  · have ha0 :
        PadicInt.toZMod P.1.1 = 0 := by
      exact ha
    simp [N13IntegralAffinePointSpecialClass.reducedPoint,
      N13IntegralAffinePointSpecialClass.reducedPointIdeal,
      N13SpecialDivisorCharts.point,
      N13SpecialDivisorCharts.affineZeroPoint,
      N13SpecialDivisorCharts.affinePointIdeal, ha0]
  · have ha1 :
        PadicInt.toZMod P.1.1 = 1 := by
      exact ha
    have ha0 :
        PadicInt.toZMod P.1.1 ≠ 0 := by
      rw [ha1]
      norm_num
    simp [N13IntegralAffinePointSpecialClass.reducedPoint,
      N13IntegralAffinePointSpecialClass.reducedPointIdeal,
      N13SpecialDivisorCharts.point,
      N13SpecialDivisorCharts.affineOnePoint,
      N13SpecialDivisorCharts.affinePointIdeal, ha0]
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
/-- The infinity component of the integral point line reduces to the
canonical infinity ideal of the same reduced point. -/
theorem restrict_integralPointTwoChartLine_infinityIdeal
    (P : IntegralPoint) :
    (N13TwoChartSpecialRestriction.restrict
      (N13FiniteAffineTwoChart.integralPointTwoChartLine P)).infinityIdeal =
      (N13SpecialDivisorCharts.point
        (N13IntegralAffinePointSpecialClass.reducedPoint P)).infinityIdeal := by
  change
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (N13FiniteAffineTwoChart.infinityClosure
          (N13IntegralAffinePointSpread.pointIdeal P)) =
      _
  exact map_infinityClosure_pointIdeal P
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13SplitQuadraticSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Restriction of the valuation-independent point line on the ordinary
affine chart is the canonical ideal of its properly reduced point. -/
theorem restrict_pointLine_affineIdeal
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y) :
    (N13TwoChartSpecialRestriction.restrict
      (N13QuadraticTwoChartSpread.pointLine x y hcurve)).affineIdeal =
      (N13SpecialDivisorCharts.point
        (reducedPoint x y hcurve)).affineIdeal := by
  rw [N13QuadraticTwoChartSpread.pointLine, reducedPoint]
  split
  · exact
      N13FiniteAffinePointInfinityClosure.restrict_integralPointTwoChartLine_affineIdeal _
  · exact
      N13EscapingPointSpecialRestriction.restrict_nonintegralPointLine_affineIdeal
        x y _ hcurve
end
end MazurProof.N13SplitQuadraticSpecialRestriction
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13SplitQuadraticSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Restriction of the same point line on the infinity chart is the canonical
ideal of the same properly reduced point. -/
theorem restrict_pointLine_infinityIdeal
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y) :
    (N13TwoChartSpecialRestriction.restrict
      (N13QuadraticTwoChartSpread.pointLine x y hcurve)).infinityIdeal =
      (N13SpecialDivisorCharts.point
        (reducedPoint x y hcurve)).infinityIdeal := by
  rw [N13QuadraticTwoChartSpread.pointLine, reducedPoint]
  split
  · exact
      N13FiniteAffinePointInfinityClosure.restrict_integralPointTwoChartLine_infinityIdeal _
  · exact
      N13EscapingPointSpecialRestriction.restrict_nonintegralPointLine_infinityIdeal
        x y _ hcurve
end
end MazurProof.N13SplitQuadraticSpecialRestriction
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13SplitQuadraticSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The affine restriction of a tensor product of two point lines equals the
canonical affine ideal of the reduced degree-two divisor. -/
theorem restrict_pairLine_affineIdeal
    (x₁ y₁ x₂ y₂ : Q₂)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    (N13TwoChartSpecialRestriction.restrict
      (N13QuadraticTwoChartSpread.pairLine
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂)).affineIdeal =
      (N13SpecialDivisorCharts.ofDivisor
        (reducedPairDivisor
          x₁ y₁ x₂ y₂ hcurve₁ hcurve₂)).affineIdeal := by
  rw [N13QuadraticTwoChartSpread.pairLine,
    N13TwoChartSpecialRestriction.restrict_tensor_affineIdeal,
    reducedPairDivisor, N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13TwoChartSpecialRestriction.restrict
      (N13QuadraticTwoChartSpread.pointLine x₁ y₁ hcurve₁)).affineIdeal *
        (N13TwoChartSpecialRestriction.restrict
          (N13QuadraticTwoChartSpread.pointLine x₂ y₂ hcurve₂)).affineIdeal =
      (N13SpecialDivisorCharts.point
          (reducedPoint x₁ y₁ hcurve₁)).affineIdeal *
        (N13SpecialDivisorCharts.point
          (reducedPoint x₂ y₂ hcurve₂)).affineIdeal
  rw [restrict_pointLine_affineIdeal, restrict_pointLine_affineIdeal]
end
end MazurProof.N13SplitQuadraticSpecialRestriction
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13SplitQuadraticSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The infinity restriction of a tensor product of two point lines equals
the canonical infinity ideal of the same reduced degree-two divisor. -/
theorem restrict_pairLine_infinityIdeal
    (x₁ y₁ x₂ y₂ : Q₂)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    (N13TwoChartSpecialRestriction.restrict
      (N13QuadraticTwoChartSpread.pairLine
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂)).infinityIdeal =
      (N13SpecialDivisorCharts.ofDivisor
        (reducedPairDivisor
          x₁ y₁ x₂ y₂ hcurve₁ hcurve₂)).infinityIdeal := by
  rw [N13QuadraticTwoChartSpread.pairLine,
    N13TwoChartSpecialRestriction.restrict_tensor_infinityIdeal,
    reducedPairDivisor, N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13TwoChartSpecialRestriction.restrict
      (N13QuadraticTwoChartSpread.pointLine x₁ y₁ hcurve₁)).infinityIdeal *
        (N13TwoChartSpecialRestriction.restrict
          (N13QuadraticTwoChartSpread.pointLine x₂ y₂ hcurve₂)).infinityIdeal =
      (N13SpecialDivisorCharts.point
          (reducedPoint x₁ y₁ hcurve₁)).infinityIdeal *
        (N13SpecialDivisorCharts.point
          (reducedPoint x₂ y₂ hcurve₂)).infinityIdeal
  rw [restrict_pointLine_infinityIdeal, restrict_pointLine_infinityIdeal]
end
end MazurProof.N13SplitQuadraticSpecialRestriction
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem solution
    (x₁ y₁ x₂ y₂ : MazurProof.N13SplitQuadraticSpecialRestriction.Q₂)
    (hcurve₁ : MazurProof.N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : MazurProof.N13GoodModelTwo.AffineEquation x₂ y₂) :
    ((MazurProof.N13TwoChartSpecialRestriction.restrict
      (MazurProof.N13QuadraticTwoChartSpread.pairLine
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂)).affineIdeal =
      (MazurProof.N13SpecialDivisorCharts.ofDivisor
        (MazurProof.N13SplitQuadraticSpecialRestriction.reducedPairDivisor
          x₁ y₁ x₂ y₂ hcurve₁ hcurve₂)).affineIdeal) ∧
    ((MazurProof.N13TwoChartSpecialRestriction.restrict
      (MazurProof.N13QuadraticTwoChartSpread.pairLine
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂)).infinityIdeal =
      (MazurProof.N13SpecialDivisorCharts.ofDivisor
        (MazurProof.N13SplitQuadraticSpecialRestriction.reducedPairDivisor
          x₁ y₁ x₂ y₂ hcurve₁ hcurve₂)).infinityIdeal) := by
  exact ⟨MazurProof.N13SplitQuadraticSpecialRestriction.restrict_pairLine_affineIdeal x₁ y₁ x₂ y₂ hcurve₁ hcurve₂, MazurProof.N13SplitQuadraticSpecialRestriction.restrict_pairLine_infinityIdeal x₁ y₁ x₂ y₂ hcurve₁ hcurve₂⟩
