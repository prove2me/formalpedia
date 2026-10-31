-- Prove2me | solution 1 for HuangN13.N13MarkedQuadraticExistence.exists_saturated_data_of_distinct_split
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:36:43.050205+00:00
-- url     : https://prove2.me/submissions/73df306a-0f8c-4682-a42a-33da32c918f2

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_OverlapBranchMapsCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_FiniteInfinityClosureCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Theorems.Thm_HuangN13_N13QuadraticTwoChartSpread_pairLine_saturated_and_marked
import Theorems.Thm_HuangN13_N13SplitQuadraticSpecialRestriction_pairLine_special_restrictions
import Theorems.Thm_MazurProof_N13GoodSexticMumfordTransport_sextic_mumfordIdeal_eq_of_dvd_sub

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
theorem xClass_mem_graphIdeal
    (xClass : R[X] →+* A) (yClass : A) (u v : R[X]) :
    xClass u ∈ graphIdeal xClass yClass u v :=
  Ideal.subset_span (by simp)
end
end MazurProof.GeneralizedGraphIdealCore
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
theorem ySubClass_mem_graphIdeal
    (xClass : R[X] →+* A) (yClass : A) (u v : R[X]) :
    ySubClass xClass yClass v ∈ graphIdeal xClass yClass u v :=
  Ideal.subset_span (by simp)
end
end MazurProof.GeneralizedGraphIdealCore
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
/-- Replacing the graph ordinate by a congruent polynomial modulo the
horizontal equation does not change the graph ideal. -/
theorem graphIdeal_eq_of_dvd_sub
    (xClass : R[X] →+* A) (yClass : A)
    (u v V : R[X]) (h : u ∣ V - v) :
    graphIdeal xClass yClass u V =
      graphIdeal xClass yClass u v := by
  obtain ⟨t, ht⟩ := h
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_graphIdeal xClass yClass u v
    · have hmultiple :
          xClass (V - v) ∈ graphIdeal xClass yClass u v := by
        rw [ht, map_mul, mul_comm]
        exact Ideal.mul_mem_left _
          (xClass t) (xClass_mem_graphIdeal xClass yClass u v)
      have heq :
          ySubClass xClass yClass V =
            ySubClass xClass yClass v - xClass (V - v) := by
        simp [ySubClass, map_sub]
      rw [heq]
      exact Ideal.sub_mem _
        (ySubClass_mem_graphIdeal xClass yClass u v) hmultiple
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_graphIdeal xClass yClass u V
    · have hmultiple :
          xClass (V - v) ∈ graphIdeal xClass yClass u V := by
        rw [ht, map_mul, mul_comm]
        exact Ideal.mul_mem_left _
          (xClass t) (xClass_mem_graphIdeal xClass yClass u V)
      have heq :
          ySubClass xClass yClass v =
            ySubClass xClass yClass V + xClass (V - v) := by
        simp [ySubClass, map_sub]
      rw [heq]
      exact Ideal.add_mem _
        (ySubClass_mem_graphIdeal xClass yClass u V) hmultiple
end
end MazurProof.GeneralizedGraphIdealCore
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
/-- Two graph ideals with coprime horizontal equations multiply to the
graph ideal of the product.  The common ordinate is only required modulo
the two factors, so this is the ideal-theoretic Chinese remainder theorem
for a split divisor. -/
theorem graphIdeal_mul_of_coprime
    (xClass : R[X] →+* A) (yClass : A)
    (u₁ u₂ v₁ v₂ V : R[X])
    (h₁ : u₁ ∣ V - v₁)
    (h₂ : u₂ ∣ V - v₂)
    (hcoprime :
      ∃ a b : R[X], a * u₁ + b * u₂ = 1) :
    graphIdeal xClass yClass u₁ v₁ *
        graphIdeal xClass yClass u₂ v₂ =
      graphIdeal xClass yClass (u₁ * u₂) V := by
  rw [← graphIdeal_eq_of_dvd_sub xClass yClass u₁ v₁ V h₁,
    ← graphIdeal_eq_of_dvd_sub xClass yClass u₂ v₂ V h₂]
  let I₁ := graphIdeal xClass yClass u₁ V
  let I₂ := graphIdeal xClass yClass u₂ V
  let I := graphIdeal xClass yClass (u₁ * u₂) V
  let g := ySubClass xClass yClass V
  apply le_antisymm
  · rw [graphIdeal, graphIdeal, graphIdeal,
      Ideal.span_pair_mul_span_pair]
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Ideal.subset_span (by simp [map_mul])
    · exact Ideal.mul_mem_left I (xClass u₁)
        (ySubClass_mem_graphIdeal xClass yClass (u₁ * u₂) V)
    · exact Ideal.mul_mem_right (xClass u₂) _
        (Ideal.subset_span
          (Set.mem_insert_iff.mpr
            (Or.inr (Set.mem_singleton _))))
    · exact Ideal.mul_mem_left I g
        (ySubClass_mem_graphIdeal xClass yClass (u₁ * u₂) V)
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [map_mul]
      exact Ideal.mul_mem_mul
        (xClass_mem_graphIdeal xClass yClass u₁ V)
        (xClass_mem_graphIdeal xClass yClass u₂ V)
    · obtain ⟨a, b, hab⟩ := hcoprime
      have h₁g :
          xClass u₁ * g ∈ I₁ * I₂ :=
        Ideal.mul_mem_mul
          (xClass_mem_graphIdeal xClass yClass u₁ V)
          (ySubClass_mem_graphIdeal xClass yClass u₂ V)
      have hg₂ :
          g * xClass u₂ ∈ I₁ * I₂ :=
        Ideal.mul_mem_mul
          (ySubClass_mem_graphIdeal xClass yClass u₁ V)
          (xClass_mem_graphIdeal xClass yClass u₂ V)
      have ha :
          xClass a * (xClass u₁ * g) ∈ I₁ * I₂ :=
        Ideal.mul_mem_left _ (xClass a) h₁g
      have hb :
          xClass b * (g * xClass u₂) ∈ I₁ * I₂ :=
        Ideal.mul_mem_left _ (xClass b) hg₂
      have hsum := Ideal.add_mem (I₁ * I₂) ha hb
      have heq :
          xClass a * (xClass u₁ * g) +
              xClass b * (g * xClass u₂) = g := by
        calc
          _ = xClass (a * u₁ + b * u₂) * g := by
            simp only [map_add, map_mul]
            ring
          _ = g := by rw [hab, map_one, one_mul]
      rw [heq] at hsum
      exact hsum
end
end MazurProof.GeneralizedGraphIdealCore
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityPointSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The generic fibre of the affine half of the point line is its
coefficient-extended, completed-square sextic graph. -/
theorem map_affinePointIdeal (P : IntegralInfinityPoint) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (affinePointIdeal P) =
      SexticMumford.mumfordIdeal Model
        (N13TwoAdicCoordinateBaseChange.mapPoly (affineU P))
        (N13GoodSexticMumfordTransport.completedGraph
          (N13TwoAdicCoordinateBaseChange.mapPoly (affineV P))) := by
  rw [N13TwoAdicCoordinateBaseChange.integralToSextic,
    ← Ideal.map_map]
  change
    Ideal.map N13GoodSexticCoordinateEquiv.toSextic
        (Ideal.map N13TwoAdicCoordinateBaseChange.extendCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (affineU P) (affineV P))) = _
  rw [N13TwoAdicCoordinateBaseChange.map_mumfordIdeal,
    N13GoodSexticMumfordTransport.map_mumfordIdeal]
end
end MazurProof.N13IntegralInfinityPointSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The affine generic fibre of the proper integral point line is exactly
the standard sextic point graph. -/
@[simp] theorem map_integralPointTwoChartLine_affineIdeal
    (P : N13IntegralAffinePointSpread.IntegralPoint) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (integralPointTwoChartLine P).affineIdeal =
      SexticMumford.mumfordIdeal Model
        (SexticMumford.pointMumford Model
          (N13IntegralAffinePointSpread.curvePoint P)).u
        (SexticMumford.pointMumford Model
          (N13IntegralAffinePointSpread.curvePoint P)).v := by
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13IntegralAffinePointSpread.pointIdeal P) =
      SexticMumford.mumfordIdeal Model
        (SexticMumford.pointMumford Model
          (N13IntegralAffinePointSpread.curvePoint P)).u
        (SexticMumford.pointMumford Model
          (N13IntegralAffinePointSpread.curvePoint P)).v
  exact N13IntegralAffinePointSpread.map_pointIdeal P
end
end MazurProof.N13FiniteAffineTwoChart
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem lift_t_coe
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    ((lift x y hx hxy).1.1 : Q₂) = x⁻¹ := by
  rfl
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem lift_v_coe
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    ((lift x y hx hxy).1.2 : Q₂) = x⁻¹ ^ 3 * y := by
  rfl
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem transportCoeffMap_lift_t
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoAdicMumfordTransport.coeffMap
        (lift x y hx hxy).1.1 = x⁻¹ := by
  exact lift_t_coe x y hx hxy
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem transportCoeffMap_lift_v
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoAdicMumfordTransport.coeffMap
        (lift x y hx hxy).1.2 = x⁻¹ ^ 3 * y := by
  exact lift_v_coe x y hx hxy
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem x_ne_zero
    (x : Q₂) (hx : x.valuation < 0) :
    x ≠ 0 :=
  N13LocalDlogRegimes.nonintegral_coordinate_ne_zero x hx
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The nonmonic affine closure equation becomes a unit multiple of the
standard monic point equation on the generic fibre. -/
theorem genericU_eq_unit_mul
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    genericU x y hx hxy =
      C (-((lift x y hx hxy).1.1 : Q₂)) *
        (X - C x) := by
  simp [genericU, N13IntegralInfinityPointSpread.affineU,
    N13TwoAdicCoordinateBaseChange.mapPoly_apply,
    N13TwoAdicCoordinateBaseChange.coeffMap,
    transportCoeffMap_lift_t, lift_t_coe]
  have hc :
      C (x⁻¹) * C x = (1 : Q₂[X]) := by
    rw [← map_mul, inv_mul_cancel₀ (x_ne_zero x hx), map_one]
  linear_combination -hc
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The completed-square graph ordinate evaluates to the standard sextic
ordinate at the generic point. -/
theorem genericV_eval
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    (genericV x y hx hxy).eval x = pointY x y := by
  simp [genericV, pointY,
    N13IntegralInfinityPointSpread.affineV,
    N13GoodSexticMumfordTransport.completedGraph,
    N13TwoAdicCoordinateBaseChange.mapPoly_apply,
    N13TwoAdicCoordinateBaseChange.coeffMap,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GoodModelTwo.h, transportCoeffMap_lift_v]
  field_simp [x_ne_zero x hx]
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem standardU_dvd_genericV_sub
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    X - C x ∣
      genericV x y hx hxy - C (pointY x y) := by
  have h :=
    X_sub_C_dvd_sub_C_eval
      (p := genericV x y hx hxy) (a := x)
  simpa [genericV_eval x y hx hxy] using h
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
private theorem span_pair_mul_left_unit
    {A : Type*} [CommRing A]
    (a x y : A) (ha : IsUnit a) :
    Ideal.span ({a * x, y} : Set A) =
      Ideal.span ({x, y} : Set A) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Ideal.mul_mem_left _
        a (Ideal.subset_span (by simp))
    · rw [hz]
      exact Ideal.subset_span (by simp)
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      obtain ⟨b, hab⟩ := isUnit_iff_exists_inv.mp ha
      have hba : b * a = 1 := by
        simpa [mul_comm] using hab
      have hax :
          a * x ∈ Ideal.span ({a * x, y} : Set A) :=
        Ideal.subset_span (by simp)
      have hbx := Ideal.mul_mem_left _ b hax
      simpa [← mul_assoc, hba] using hbx
    · rw [hz]
      exact Ideal.subset_span (by simp)
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem genericU_scalar_isUnit
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    IsUnit
      (SexticMumford.xClass Model
        (C (-((lift x y hx hxy).1.1 : Q₂)))) := by
  have ht :
      -((lift x y hx hxy).1.1 : Q₂) ≠ 0 := by
    simp [lift_t_coe, x_ne_zero x hx]
  have hu : IsUnit (-((lift x y hx hxy).1.1 : Q₂)) :=
    isUnit_iff_ne_zero.mpr ht
  change
    IsUnit
      (algebraMap Q₂
        (SexticMumford.CoordinateRing Model)
        (-((lift x y hx hxy).1.1 : Q₂)))
  exact
    hu.map
      (algebraMap Q₂
        (SexticMumford.CoordinateRing Model))
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem mumfordIdeal_genericU_eq_standardU
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    SexticMumford.mumfordIdeal Model
        (genericU x y hx hxy)
        (genericV x y hx hxy) =
      SexticMumford.mumfordIdeal Model
        (X - C x) (genericV x y hx hxy) := by
  rw [SexticMumford.mumfordIdeal,
    genericU_eq_unit_mul,
    SexticMumford.xClass_mul]
  exact
    span_pair_mul_left_unit
      (SexticMumford.xClass Model
        (C (-((lift x y hx hxy).1.1 : Q₂))))
      (SexticMumford.xClass Model (X - C x))
      (SexticMumford.ySubClass Model
        (genericV x y hx hxy))
      (genericU_scalar_isUnit x y hx hxy)
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13EscapingDegreeOneSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The generic fibre of the escaping two-chart line is exactly the
standard sextic point graph. -/
theorem genericIdeal_eq_standardPoint
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13IntegralInfinityPointSpread.affinePointIdeal
          (lift x y hx hxy)) =
      SexticMumford.mumfordIdeal Model
        (X - C x) (C (pointY x y)) := by
  rw [N13IntegralInfinityPointSpread.map_affinePointIdeal]
  change
    SexticMumford.mumfordIdeal Model
        (genericU x y hx hxy)
        (genericV x y hx hxy) =
      _
  rw [mumfordIdeal_genericU_eq_standardU]
  exact
    N13GoodSexticMumfordTransport.sextic_mumfordIdeal_eq_of_dvd_sub
      (X - C x) (genericV x y hx hxy) (C (pointY x y))
      (standardU_dvd_genericV_sub x y hx hxy)
end
end MazurProof.N13EscapingDegreeOneSpread
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
@[simp] theorem tensor_affineIdeal (L M : TwoChartLine) :
    (tensor L M).affineIdeal =
      L.affineIdeal * M.affineIdeal :=
  rfl
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem map_tensor_affineIdeal
    (L M : TwoChartLine) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (tensor L M).affineIdeal =
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal *
        Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          M.affineIdeal := by
  rw [tensor_affineIdeal, Ideal.map_mul]
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem secantV_eval_left
    (x₁ z₁ x₂ z₂ : N13EscapingDegreeOneSpread.Q₂) :
    (secantV x₁ z₁ x₂ z₂).eval x₁ = z₁ := by
  simp [secantV]
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem secantV_eval_right
    (x₁ z₁ x₂ z₂ : N13EscapingDegreeOneSpread.Q₂)
    (hneq : x₁ ≠ x₂) :
    (secantV x₁ z₁ x₂ z₂).eval x₂ = z₂ := by
  have hd : x₂ - x₁ ≠ 0 :=
    sub_ne_zero.mpr hneq.symm
  simp [secantV, hd]
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
private theorem linearFactors_coprime
    (x₁ x₂ : N13EscapingDegreeOneSpread.Q₂)
    (hneq : x₁ ≠ x₂) :
    ∃ a b : N13EscapingDegreeOneSpread.Q₂[X],
      a * (X - C x₁) + b * (X - C x₂) = 1 := by
  have hd : x₂ - x₁ ≠ 0 :=
    sub_ne_zero.mpr hneq.symm
  refine
    ⟨C ((x₂ - x₁)⁻¹), -C ((x₂ - x₁)⁻¹), ?_⟩
  calc
    C ((x₂ - x₁)⁻¹) * (X - C x₁) +
          -C ((x₂ - x₁)⁻¹) * (X - C x₂) =
        C ((x₂ - x₁)⁻¹) * C (x₂ - x₁) := by
      rw [map_sub]
      ring
    _ = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hd, map_one]
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The product of two distinct point graphs is the quadratic graph of
their secant interpolant. -/
theorem pointIdeal_mul_eq_secantGraph
    (x₁ z₁ x₂ z₂ : N13EscapingDegreeOneSpread.Q₂)
    (hneq : x₁ ≠ x₂) :
    SexticMumford.mumfordIdeal
          N13EscapingDegreeOneSpread.Model
          (X - C x₁) (C z₁) *
        SexticMumford.mumfordIdeal
          N13EscapingDegreeOneSpread.Model
          (X - C x₂) (C z₂) =
      SexticMumford.mumfordIdeal
        N13EscapingDegreeOneSpread.Model
        ((X - C x₁) * (X - C x₂))
        (secantV x₁ z₁ x₂ z₂) := by
  have h₁ :
      X - C x₁ ∣ secantV x₁ z₁ x₂ z₂ - C z₁ := by
    simpa using
      (X_sub_C_dvd_sub_C_eval
        (p := secantV x₁ z₁ x₂ z₂) (a := x₁))
  have h₂ :
      X - C x₂ ∣ secantV x₁ z₁ x₂ z₂ - C z₂ := by
    simpa [secantV_eval_right x₁ z₁ x₂ z₂ hneq] using
      (X_sub_C_dvd_sub_C_eval
        (p := secantV x₁ z₁ x₂ z₂) (a := x₂))
  simpa [SexticMumford.mumfordIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    SexticMumford.ySubClass,
    GeneralizedGraphIdealCore.ySubClass,
    SexticMumford.xClassHom_apply] using
      (GeneralizedGraphIdealCore.graphIdeal_mul_of_coprime
        (SexticMumford.xClassHom
          N13EscapingDegreeOneSpread.Model)
        (SexticMumford.yClass
          N13EscapingDegreeOneSpread.Model)
        (X - C x₁) (X - C x₂) (C z₁) (C z₂)
        (secantV x₁ z₁ x₂ z₂)
        h₁ h₂ (linearFactors_coprime x₁ x₂ hneq))
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- A reduced ordinate on a split monic quadratic is its secant
interpolant. -/
theorem mumford_v_eq_secant
    (D : SexticMumford.Mumford
      N13EscapingDegreeOneSpread.Model)
    (hdeg : D.u.natDegree = 2)
    (x₁ x₂ : N13EscapingDegreeOneSpread.Q₂)
    (hneq : x₁ ≠ x₂) :
    D.v =
      secantV x₁ (D.v.eval x₁) x₂ (D.v.eval x₂) := by
  have huDegree :
      D.u.degree = (2 : WithBot ℕ) := by
    rw [degree_eq_natDegree D.u_monic.ne_zero, hdeg]
    norm_num
  have hvDegree :
      D.v.degree < D.u.degree :=
    (mod_eq_self_iff D.u_monic.ne_zero).mp D.v_reduced
  have hvlt : D.v.natDegree < 2 := by
    by_cases hv0 : D.v = 0
    · simp [hv0]
    · rw [natDegree_lt_iff_degree_lt hv0]
      simpa [huDegree] using hvDegree
  have hsle :
      (secantV x₁ (D.v.eval x₁) x₂ (D.v.eval x₂)).natDegree ≤ 1 := by
    unfold secantV
    compute_degree
  let f : Fin 2 → N13EscapingDegreeOneSpread.Q₂ :=
    fun i => if i = 0 then x₁ else x₂
  have hf : Function.Injective f := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [f, hneq, hneq.symm]
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    D.v
    (secantV x₁ (D.v.eval x₁) x₂ (D.v.eval x₂))
    hf
  · intro i
    fin_cases i
    · simp [f]
    · simp [f, secantV_eval_right _ _ _ _ hneq]
  · simp only [Fintype.card_fin]
    omega
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The two factors of a split Mumford horizontal polynomial are actual
curve points. -/
theorem mumford_eval_onCurve_of_split
    (D : SexticMumford.Mumford
      N13EscapingDegreeOneSpread.Model)
    (x₁ x₂ : N13EscapingDegreeOneSpread.Q₂)
    (hfactor :
      D.u = (X - C x₁) * (X - C x₂)) :
    (D.v.eval x₁) ^ 2 =
        N13EscapingDegreeOneSpread.Model.f.eval x₁ ∧
      (D.v.eval x₂) ^ 2 =
        N13EscapingDegreeOneSpread.Model.f.eval x₂ := by
  obtain ⟨w, hw⟩ := D.curve_dvd
  constructor
  · have hzero :=
      congrArg (Polynomial.eval x₁) hw
    simp [hfactor] at hzero
    exact (sub_eq_zero.mp hzero).symm
  · have hzero :=
      congrArg (Polynomial.eval x₂) hw
    simp [hfactor] at hzero
    exact (sub_eq_zero.mp hzero).symm
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- A split balanced quadratic Mumford graph is literally the product of
the two point ideals, not only equal to it in the Picard quotient. -/
theorem mumfordIdeal_eq_pointIdeal_mul_of_split
    (D : SexticMumford.Mumford
      N13EscapingDegreeOneSpread.Model)
    (hdeg : D.u.natDegree = 2)
    (x₁ x₂ : N13EscapingDegreeOneSpread.Q₂)
    (hfactor :
      D.u = (X - C x₁) * (X - C x₂))
    (hneq : x₁ ≠ x₂) :
    SexticMumford.mumfordIdeal
          N13EscapingDegreeOneSpread.Model
          (X - C x₁) (C (D.v.eval x₁)) *
        SexticMumford.mumfordIdeal
          N13EscapingDegreeOneSpread.Model
          (X - C x₂) (C (D.v.eval x₂)) =
      SexticMumford.mumfordIdeal
        N13EscapingDegreeOneSpread.Model D.u D.v := by
  rw [pointIdeal_mul_eq_secantGraph _ _ _ _ hneq,
    ← hfactor, ← mumford_v_eq_secant
      D hdeg x₁ x₂ hneq]
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Inverse completed-square ordinate over `ℚ₂`. -/
def goodY
    (x Y : N13EscapingDegreeOneSpread.Q₂) :
    N13EscapingDegreeOneSpread.Q₂ :=
  (Y - N13GoodModelTwo.h x) / 2
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem pointY_goodY
    (x Y : N13EscapingDegreeOneSpread.Q₂) :
    N13EscapingDegreeOneSpread.pointY x (goodY x Y) = Y := by
  simp only [N13EscapingDegreeOneSpread.pointY, goodY]
  ring
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Completing the square is an equivalence between the sextic and good
affine equations over `ℚ₂`. -/
theorem goodY_onCurve
    (x Y : N13EscapingDegreeOneSpread.Q₂)
    (hcurve :
      Y ^ 2 =
        N13EscapingDegreeOneSpread.Model.f.eval x) :
    N13GoodModelTwo.AffineEquation x (goodY x Y) := by
  have hf :
      N13GoodModelTwo.completedSextic x =
        N13EscapingDegreeOneSpread.Model.f.eval x := by
    simp [N13EscapingDegreeOneSpread.Model,
      N13Mumford.f, N13GoodModelTwo.completedSextic]
  have hs :=
    N13GoodModelTwo.completed_square_identity x (goodY x Y)
  have hround :
      2 * goodY x Y + N13GoodModelTwo.h x = Y := by
    exact pointY_goodY x Y
  rw [hround] at hs
  have hfour :
      (4 : N13EscapingDegreeOneSpread.Q₂) *
          ((goodY x Y) ^ 2 +
            N13GoodModelTwo.h x * goodY x Y -
            N13GoodModelTwo.rhs x) = 0 := by
    rw [hf, ← hcurve] at hs
    calc
      _ =
          (Y ^ 2 +
            4 * ((goodY x Y) ^ 2 +
              N13GoodModelTwo.h x * goodY x Y -
              N13GoodModelTwo.rhs x)) -
            Y ^ 2 := by ring
      _ = 0 := by rw [← hs, sub_self]
  have hres :
      (goodY x Y) ^ 2 +
          N13GoodModelTwo.h x * goodY x Y -
        N13GoodModelTwo.rhs x = 0 :=
    (mul_eq_zero.mp hfour).resolve_left (by norm_num)
  exact sub_eq_zero.mp hres
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13IntegralFractionalHull.integralFunctionFieldFractionRing MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Coercing the generic ideal unit to a fractional ideal recovers the
literal extension of the line's affine ideal.

This bridge is independent of the geometric origin of the proper line and is
therefore shared by point and quadratic Picard realizations. -/
@[simp] theorem coe_genericIdealUnit
    (L : Line) :
    (genericIdealUnit L :
        N13IntegralFractionalHull.RationalFractionalIdeal) =
      (Ideal.map
        N13IntegralFractionalHull.integralToRational
        L.affineIdeal :
        N13IntegralFractionalHull.RationalFractionalIdeal) := by
  change
    N13IntegralFractionalHull.extendFractional
        (L.affine_isUnit.unit :
          N13IntegralFractionalHull.IntegralFractionalIdeal) =
      _
  rw [L.affine_isUnit.unit_spec,
    N13IntegralFractionalHull.extendFractional,
    FractionalIdeal.extendedHom'_apply,
    FractionalIdeal.extended_coeIdeal_eq_map]
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Equality of mapped generic affine ideals determines equality of their
packaged fractional-ideal units.

The statement retains the exact Mumford representative rather than passing
prematurely to the oriented Picard quotient. -/
theorem genericIdealUnit_eq_mumfordIdealUnit_of_map_affineIdeal_eq
    (L : Line)
    (D : SexticMumford.Mumford Model)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    genericIdealUnit L =
      SexticMumford.mumfordIdealUnit Model D.toSemi := by
  apply Units.ext
  rw [coe_genericIdealUnit,
    SexticMumford.coe_mumfordIdealUnit]
  exact
    congrArg
      (fun I : Ideal N13IntegralFractionalHull.RationalRing =>
        (I : N13IntegralFractionalHull.RationalFractionalIdeal))
      hmap
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A proper line with the exact Mumford affine ideal realizes the literal
oriented Mumford datum when marked by the representative's exponent
`nInf - 1`.

This is the generic-fibre bridge used uniformly by point and quadratic
two-chart realizations. -/
theorem genericRaw_eq_mumfordRaw_of_map_affineIdeal_eq
    (L : Line)
    (D : SexticMumford.Mumford Model)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    genericRaw L ((D.nInf : ℤ) - 1) =
      SexticMumford.mumfordRaw Model D := by
  apply Prod.ext
  · exact
      genericIdealUnit_eq_mumfordIdealUnit_of_map_affineIdeal_eq
        L D hmap
  · rfl
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Exact mapped-ideal equality also identifies the induced generic Picard
class with the standard oriented class of the Mumford representative. -/
theorem genericClass_eq_classOf_of_map_affineIdeal_eq
    (L : Line)
    (D : SexticMumford.Mumford Model)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    genericClass L ((D.nInf : ℤ) - 1) =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder Q₂)
        D := by
  unfold genericClass SexticMumford.classOf
  rw [genericRaw_eq_mumfordRaw_of_map_affineIdeal_eq L D hmap]
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13QuadraticTwoChartSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The generic affine ideal of the integral point line is the standard
sextic point graph. -/
theorem map_integralPointLine_affineIdeal
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y)
    (hx : ‖x‖ ≤ 1) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (integralPointLine x y hcurve hx).affineIdeal =
      SexticMumford.mumfordIdeal Model
        (X - C x)
        (C (N13EscapingDegreeOneSpread.pointY x y)) := by
  let P : N13IntegralAffinePointSpread.IntegralPoint :=
    N13ProperCurveReduction.integralAffineLift x y hx hcurve
  have hmap :=
    N13FiniteAffineTwoChart.map_integralPointTwoChartLine_affineIdeal P
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P).affineIdeal =
      _
  rw [hmap]
  simp [P,
    N13ProperCurveReduction.integralAffineLift,
    N13IntegralAffinePointSpread.curvePoint,
    N13IntegralAffinePointSpread.sexticY,
    N13EscapingDegreeOneSpread.pointY,
    SexticMumford.pointMumford,
    SexticMumford.affinePointMumford]
end
end MazurProof.N13QuadraticTwoChartSpread
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13QuadraticTwoChartSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The generic affine ideal of the escaping point line is the same standard
sextic point graph. -/
theorem map_escapingPointLine_affineIdeal
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y)
    (hx : x.valuation < 0) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (escapingPointLine x y hcurve hx).affineIdeal =
      SexticMumford.mumfordIdeal Model
        (X - C x)
        (C (N13EscapingDegreeOneSpread.pointY x y)) := by
  exact
    N13EscapingDegreeOneSpread.genericIdeal_eq_standardPoint
      x y hx hcurve
end
end MazurProof.N13QuadraticTwoChartSpread
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13QuadraticTwoChartSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The valuation-independent point line always has the standard point graph
as its generic affine ideal. -/
theorem map_pointLine_affineIdeal
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (pointLine x y hcurve).affineIdeal =
      SexticMumford.mumfordIdeal Model
        (X - C x)
        (C (N13EscapingDegreeOneSpread.pointY x y)) := by
  rw [pointLine]
  split
  · exact map_integralPointLine_affineIdeal x y hcurve _
  · exact map_escapingPointLine_affineIdeal x y hcurve _
end
end MazurProof.N13QuadraticTwoChartSpread
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13QuadraticTwoChartSpread
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The generic affine ideal of the pair line is the product of the two
standard point graph ideals. -/
theorem map_pairLine_affineIdeal
    (x₁ y₁ x₂ y₂ : Q₂)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (pairLine x₁ y₁ x₂ y₂ hcurve₁ hcurve₂).affineIdeal =
      SexticMumford.mumfordIdeal Model
          (X - C x₁)
          (C (N13EscapingDegreeOneSpread.pointY x₁ y₁)) *
        SexticMumford.mumfordIdeal Model
          (X - C x₂)
          (C (N13EscapingDegreeOneSpread.pointY x₂ y₂)) := by
  rw [pairLine, N13TwoChartLineTensor.map_tensor_affineIdeal,
    map_pointLine_affineIdeal, map_pointLine_affineIdeal]
end
end MazurProof.N13QuadraticTwoChartSpread
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SplitQuadraticPicardRealization
noncomputable section
/-- Proper two-chart lines on the integral good model. -/
abbrev Line : Type :=
  N13TwoChartPicardRealization.Line
end
end MazurProof.N13SplitQuadraticPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SplitQuadraticPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- Package one proper line and its two exact special chart comparisons as
two-fibre Picard data for a chosen Mumford representative.

The generic affine ideal equality is not needed to construct the data; it is
consumed separately to identify the resulting generic class. -/
def dataOfSpecialRealization
    (D : SexticMumford.Mumford Model)
    (L : Line)
    (Δ : EffectiveDivisorTwo)
    (haffine :
      (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal)
    (hinfinity :
      (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal) :
    N13TwoChartPicardRealization.Data where
  charts := L
  infinityOrder := (D.nInf : ℤ) - 1
  specialDivisor := Δ
  special_affine := haffine
  special_infinity := hinfinity
end
end MazurProof.N13SplitQuadraticPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SplitQuadraticPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- Packaging a line with its special divisor does not alter its affine
lattice, so a vertical-saturation certificate passes through definitionally. -/
theorem dataOfSpecialRealization_affineVerticallySaturated
    (D : SexticMumford.Mumford Model)
    (L : Line)
    (Δ : EffectiveDivisorTwo)
    (haffine :
      (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal)
    (hinfinity :
      (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal)
    (hL : N13TwoChartPicardRealization.AffineVerticallySaturated L) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (dataOfSpecialRealization D L Δ haffine hinfinity).charts := by
  exact hL
end
end MazurProof.N13SplitQuadraticPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SplitQuadraticPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Exact generic affine-ideal equality identifies the raw generic datum of
`dataOfSpecialRealization` with the literal Mumford raw datum. -/
theorem dataOfSpecialRealization_genericRaw_eq_mumfordRaw
    (D : SexticMumford.Mumford Model)
    (L : Line)
    (Δ : EffectiveDivisorTwo)
    (haffine :
      (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal)
    (hinfinity :
      (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    N13TwoChartPicardRealization.genericRaw
        (dataOfSpecialRealization
          D L Δ haffine hinfinity).charts
        (dataOfSpecialRealization
          D L Δ haffine hinfinity).infinityOrder =
      SexticMumford.mumfordRaw Model D := by
  change
    N13TwoChartPicardRealization.genericRaw
        L ((D.nInf : ℤ) - 1) =
      SexticMumford.mumfordRaw Model D
  exact
    N13TwoChartPicardRealization.genericRaw_eq_mumfordRaw_of_map_affineIdeal_eq
      L D hmap
end
end MazurProof.N13SplitQuadraticPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SplitQuadraticPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The generic Picard class of the packaged realization is the standard
oriented class of the same Mumford representative. -/
theorem dataOfSpecialRealization_toGenericPic_eq_classOf
    (D : SexticMumford.Mumford Model)
    (L : Line)
    (Δ : EffectiveDivisorTwo)
    (haffine :
      (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal)
    (hinfinity :
      (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    (dataOfSpecialRealization
      D L Δ haffine hinfinity).toGenericPic =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder
          N13TwoChartPicardRealization.Q₂)
        D := by
  change
    N13TwoChartPicardRealization.genericClass
        L ((D.nInf : ℤ) - 1) =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder
          N13TwoChartPicardRealization.Q₂)
        D
  exact
    N13TwoChartPicardRealization.genericClass_eq_classOf_of_map_affineIdeal_eq
      L D hmap
end
end MazurProof.N13SplitQuadraticPicardRealization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MarkedQuadraticExistence
noncomputable section
open Polynomial N13InfinityChartMarking
open N13SplitQuadraticPicardRealization N13SplitQuadraticSpecialRestriction
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem exists_saturated_twoChartLine_and_specialDivisor_of_distinct_split
    (D : SexticMumford.Mumford N13QuadraticTwoChartSpread.Model)
    (hdeg : D.u.natDegree = 2)
    (x₁ x₂ : Q₂)
    (hfactor : D.u = (Polynomial.X - Polynomial.C x₁) *
      (Polynomial.X - Polynomial.C x₂))
    (hneq : x₁ ≠ x₂) :
    ∃ L : N13QuadraticTwoChartSpread.TwoChartLine,
      ∃ Δ : N13SpecialDivisorCharts.EffectiveDivisorTwo,
        Ideal.map
            N13TwoAdicCoordinateBaseChange.integralToSextic
            L.affineIdeal =
          SexticMumford.mumfordIdeal
            N13QuadraticTwoChartSpread.Model D.u D.v ∧
        (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
          (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal ∧
        (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
          (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal ∧
        N13TwoChartPicardRealization.AffineVerticallySaturated L ∧
        HasInfinityMultiplicities L 0 0 := by
  obtain ⟨hsextic₁, hsextic₂⟩ :=
    N13TwoChartLineTensor.mumford_eval_onCurve_of_split
      D x₁ x₂ hfactor
  let y₁ :=
    N13TwoChartLineTensor.goodY x₁ (D.v.eval x₁)
  let y₂ :=
    N13TwoChartLineTensor.goodY x₂ (D.v.eval x₂)
  have hcurve₁ :
      N13GoodModelTwo.AffineEquation x₁ y₁ :=
    N13TwoChartLineTensor.goodY_onCurve
      x₁ (D.v.eval x₁) hsextic₁
  have hcurve₂ :
      N13GoodModelTwo.AffineEquation x₂ y₂ :=
    N13TwoChartLineTensor.goodY_onCurve
      x₂ (D.v.eval x₂) hsextic₂
  let L :=
    N13QuadraticTwoChartSpread.pairLine
      x₁ y₁ x₂ y₂ hcurve₁ hcurve₂
  let Δ :=
    reducedPairDivisor x₁ y₁ x₂ y₂ hcurve₁ hcurve₂
  refine ⟨L, Δ, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [L]
    rw [N13QuadraticTwoChartSpread.map_pairLine_affineIdeal,
      N13TwoChartLineTensor.pointY_goodY,
      N13TwoChartLineTensor.pointY_goodY,
      N13TwoChartLineTensor.mumfordIdeal_eq_pointIdeal_mul_of_split
        D hdeg x₁ x₂ hfactor hneq]
  · exact
      (fun x₁ y₁ x₂ y₂ hcurve₁ hcurve₂ => (HuangN13.N13SplitQuadraticSpecialRestriction.pairLine_special_restrictions x₁ y₁ x₂ y₂ hcurve₁ hcurve₂).1)
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂
  · exact
      (fun x₁ y₁ x₂ y₂ hcurve₁ hcurve₂ => (HuangN13.N13SplitQuadraticSpecialRestriction.pairLine_special_restrictions x₁ y₁ x₂ y₂ hcurve₁ hcurve₂).2)
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂
  · exact
      (HuangN13.N13QuadraticTwoChartSpread.pairLine_saturated_and_marked).1
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂
  · exact (HuangN13.N13QuadraticTwoChartSpread.pairLine_saturated_and_marked).2 x₁ y₁ x₂ y₂ hcurve₁ hcurve₂
end
end MazurProof.N13MarkedQuadraticExistence
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MarkedQuadraticExistence
noncomputable section
open Polynomial N13InfinityChartMarking
open N13SplitQuadraticPicardRealization N13SplitQuadraticSpecialRestriction
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem exists_saturated_data_of_distinct_split
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (x₁ x₂ : N13SplitQuadraticSpecialRestriction.Q₂)
    (hfactor :
      D.u = (Polynomial.X - Polynomial.C x₁) *
        (Polynomial.X - Polynomial.C x₂))
    (hneq : x₁ ≠ x₂) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          Model
          (N13Infinity.positiveInfinityOrder
            N13TwoChartPicardRealization.Q₂)
          D ∧
      N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      HasInfinityMultiplicities R.charts 0 0 := by
  obtain ⟨L, Δ, hmap, haffine, hinfinity, hsaturated, hmarked⟩ :=
    exists_saturated_twoChartLine_and_specialDivisor_of_distinct_split
      D hdeg x₁ x₂ hfactor hneq
  let R :=
    dataOfSpecialRealization D L Δ haffine hinfinity
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · exact
      dataOfSpecialRealization_genericRaw_eq_mumfordRaw
        D L Δ haffine hinfinity hmap
  · exact
      dataOfSpecialRealization_toGenericPic_eq_classOf
        D L Δ haffine hinfinity hmap
  · exact
      dataOfSpecialRealization_affineVerticallySaturated
        D L Δ haffine hinfinity hsaturated
  · exact hmarked
end
end MazurProof.N13MarkedQuadraticExistence
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
theorem solution
    (D : MazurProof.SexticMumford.Mumford MazurProof.N13MarkedQuadraticExistence.Model)
    (hdeg : D.u.natDegree = 2)
    (x₁ x₂ : MazurProof.N13SplitQuadraticSpecialRestriction.Q₂)
    (hfactor :
      D.u = (Polynomial.X - Polynomial.C x₁) *
        (Polynomial.X - Polynomial.C x₂))
    (hneq : x₁ ≠ x₂) :
    ∃ R : MazurProof.N13TwoChartPicardRealization.Data,
      MazurProof.N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        MazurProof.SexticMumford.mumfordRaw MazurProof.N13MarkedQuadraticExistence.Model D ∧
      R.toGenericPic =
        MazurProof.SexticMumford.classOf
          MazurProof.N13MarkedQuadraticExistence.Model
          (MazurProof.N13Infinity.positiveInfinityOrder
            MazurProof.N13TwoChartPicardRealization.Q₂)
          D ∧
      MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities R.charts 0 0 := by
  exact MazurProof.N13MarkedQuadraticExistence.exists_saturated_data_of_distinct_split D hdeg x₁ x₂ hfactor hneq
