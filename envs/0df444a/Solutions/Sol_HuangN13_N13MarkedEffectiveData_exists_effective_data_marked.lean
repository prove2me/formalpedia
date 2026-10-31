-- Prove2me | solution 1 for HuangN13.N13MarkedEffectiveData.exists_effective_data_marked
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T15:16:49.545738+00:00
-- url     : https://prove2.me/submissions/fb0be190-512e-4063-a1cb-af8d7432822a

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore
import Theorems.Thm_HuangN13_N13MarkedEffectiveData_anchoredPointData_multiplicities
import Theorems.Thm_HuangN13_N13MarkedQuadraticExistence_exists_saturated_data
import Theorems.Thm_MazurProof_N13EscapingPointPicardRealization_affinePointIdeal_scalarSaturated
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_scalar_saturated
import Theorems.Thm_MazurProof_N13GoodSexticMumfordTransport_sextic_mumfordIdeal_eq_of_dvd_sub
import Theorems.Thm_MazurProof_N13IntegralInfinityPointSpread_pointIdeal_isUnit
import Theorems.Thm_MazurProof_N13QuadraticTwoChartSpreadSaturation_mul_scalar_saturated_of_left_isUnit

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
/-- A degree-one balanced graph with no infinity contribution is exactly
the Mumford representative of an affine curve point. -/
theorem exists_affinePoint_of_natDegree_eq_one
    (D : Mumford M)
    (hdeg : D.u.natDegree = 1)
    (hnInf : D.nInf = 0) :
    ∃ x y : K, ∃ hcurve : y ^ 2 = M.f.eval x,
      D = affinePointMumford M x y hcurve := by
  let x : K := -D.u.coeff 0
  let y : K := D.v.coeff 0
  have hu :
      D.u = X - C x := by
    rw [D.u_monic.eq_X_add_C hdeg]
    simp [x]
  have huDegree :
      D.u.degree = (1 : WithBot ℕ) := by
    rw [degree_eq_natDegree D.u_monic.ne_zero, hdeg]
    norm_num
  have hvDegree :
      D.v.degree < D.u.degree :=
    (mod_eq_self_iff D.u_monic.ne_zero).mp D.v_reduced
  have hvNatDegree :
      D.v.natDegree = 0 := by
    by_cases hv0 : D.v = 0
    · simp [hv0]
    · have hvlt : D.v.natDegree < 1 := by
        rw [natDegree_lt_iff_degree_lt hv0]
        simpa [huDegree] using hvDegree
      omega
  have hv :
      D.v = C y := by
    exact eq_C_of_natDegree_eq_zero hvNatDegree
  have hzero :
      (M.f - D.v ^ 2).eval x = 0 := by
    obtain ⟨q, hq⟩ := D.curve_dvd
    rw [hq, eval_mul, hu]
    simp
  have hcurve :
      y ^ 2 = M.f.eval x := by
    have hzero' :
        M.f.eval x - y ^ 2 = 0 := by
      simpa [hv] using hzero
    exact (sub_eq_zero.mp hzero').symm
  refine ⟨x, y, hcurve, ?_⟩
  cases D with
  | mk u v n u_monic deg_u v_reduced curve_dvd infinity_bound =>
      dsimp at hu hv hnInf ⊢
      congr
end
end MazurProof.SexticMumford
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
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A line trivial on the affine chart is vertically saturated.  This covers
the degree-zero spread, whose divisor is supported entirely at infinity. -/
theorem affineVerticallySaturated_of_affineIdeal_eq_top
    (L : Line) (hL : L.affineIdeal = ⊤) :
    AffineVerticallySaturated L := by
  simp [AffineVerticallySaturated, hL]
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
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A line whose affine lattice is a monic generalized Mumford graph is
vertically saturated because its quotient is free over the coefficient
domain. -/
theorem affineVerticallySaturated_of_affineIdeal_eq_mumfordIdeal
    (L : Line)
    (D : N13GeneralizedMumfordIntegral.SemiMumford
      (R := N13IntegralModelContraction.R₂))
    (hL :
      L.affineIdeal =
        N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v) :
    AffineVerticallySaturated L := by
  intro r hr a ha
  rw [hL] at ha ⊢
  change
    N13GeneralizedMumfordIntegral.xClass
          (Polynomial.C r) * a ∈
        N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v at ha
  exact
    N13GeneralizedMumfordIntegral.scalar_saturated
      D r hr a ha
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
/-- Equality of literal oriented raw data recovers equality of the underlying
generic affine ideals.

The first component of the raw datum is an invertible fractional ideal.
After forgetting its unit structure, injectivity of the embedding from
ordinary ideals into fractional ideals recovers the original ideal equality.
The infinity component is irrelevant for this projection. -/
theorem map_affineIdeal_eq_of_genericRaw_eq_mumfordRaw
    (L : Line) (infinityOrder : ℤ)
    (D : SexticMumford.Mumford Model)
    (hraw :
      genericRaw L infinityOrder =
        SexticMumford.mumfordRaw Model D) :
    Ideal.map
        N13IntegralFractionalHull.integralToRational
        L.affineIdeal =
      SexticMumford.mumfordIdeal Model D.u D.v := by
  have hunit :
      genericIdealUnit L =
        SexticMumford.mumfordIdealUnit Model D.toSemi :=
    congrArg Prod.fst hraw
  have hfrac := congrArg
    (fun I : Units N13IntegralFractionalHull.RationalFractionalIdeal =>
      (I : N13IntegralFractionalHull.RationalFractionalIdeal))
    hunit
  rw [coe_genericIdealUnit,
    SexticMumford.coe_mumfordIdealUnit] at hfrac
  exact FractionalIdeal.coeIdeal_injective hfrac
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
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The literal integral affine-point line is vertically saturated.  Its
affine lattice is a monic generalized Mumford graph, whose quotient has the
standard free coefficient basis. -/
theorem integralPointTwoChartLine_affineVerticallySaturated
    (P : IntegralPoint) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13FiniteAffineTwoChart.integralPointTwoChartLine P) := by
  apply
    N13TwoChartPicardRealization.affineVerticallySaturated_of_affineIdeal_eq_mumfordIdeal
      _ (N13IntegralAffinePointSpread.integralSemiGraph P)
  rfl
end
end MazurProof.N13IntegralPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13EscapingPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The proper two-chart line of a nonintegral affine point is vertically
saturated on its ordinary affine chart. -/
theorem nonintegralPointLine_affineVerticallySaturated
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13IntegralInfinityPointSpread.nonintegralPointLine
        x y hx hxy) := by
  intro r hr a ha
  exact
    affinePointIdeal_scalarSaturated
      (N13ProperCurveReduction.nonintegralInfinityLift
        x y hx hxy)
      r hr a ha
end
end MazurProof.N13EscapingPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13QuadraticTwoChartSpreadSaturation
noncomputable section
/-- Tensoring two vertically saturated two-chart lines preserves vertical
saturation on the affine chart.  Invertibility of the first affine ideal is
the essential hypothesis supplied by the line structure. -/
theorem affineVerticallySaturated_tensor
    (L M : N13TwoChartPicardRealization.Line)
    (hL : N13TwoChartPicardRealization.AffineVerticallySaturated L)
    (hM : N13TwoChartPicardRealization.AffineVerticallySaturated M) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13TwoChartLineTensor.tensor L M) := by
  change
    ∀ (r : R₂), r ≠ 0 → ∀ a : A,
      algebraMap R₂ A r * a ∈ L.affineIdeal * M.affineIdeal →
        a ∈ L.affineIdeal * M.affineIdeal
  exact
    mul_scalar_saturated_of_left_isUnit
      L.affineIdeal M.affineIdeal L.affine_isUnit hL hM
end
end MazurProof.N13QuadraticTwoChartSpreadSaturation
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13QuadraticTwoChartSpreadSaturation
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Every valuation-independent point line is vertically saturated on the
ordinary affine chart. -/
theorem pointLine_affineVerticallySaturated
    (x y : N13QuadraticTwoChartSpread.Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13QuadraticTwoChartSpread.pointLine x y hcurve) := by
  rw [N13QuadraticTwoChartSpread.pointLine]
  split
  · let P : N13IntegralAffinePointSpread.IntegralPoint :=
      N13ProperCurveReduction.integralAffineLift x y ‹‖x‖ ≤ 1› hcurve
    change
      N13TwoChartPicardRealization.AffineVerticallySaturated
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P)
    exact
      N13IntegralPointPicardRealization.integralPointTwoChartLine_affineVerticallySaturated P
  · exact
      N13EscapingPointPicardRealization.nonintegralPointLine_affineVerticallySaturated
        x y _ hcurve
end
end MazurProof.N13QuadraticTwoChartSpreadSaturation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveGraphData
noncomputable section
open Polynomial
open scoped Sym2
open N13TwoChartPicardRealization N13EffectiveInfinityRepair
open N13.TwoChartTensorCompatibility
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem infinityLine_affineIdeal (b : Bool) : (infinityLine b).affineIdeal = ⊤ := by
  cases b <;> simp [infinityLine]
end
end MazurProof.N13EffectiveGraphData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveGraphData
noncomputable section
open Polynomial
open scoped Sym2
open N13TwoChartPicardRealization N13EffectiveInfinityRepair
open N13.TwoChartTensorCompatibility
theorem infinityLine_saturated (b : Bool) : AffineVerticallySaturated (infinityLine b) :=
  affineVerticallySaturated_of_affineIdeal_eq_top _ (infinityLine_affineIdeal b)
end
end MazurProof.N13EffectiveGraphData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveGraphData
noncomputable section
open Polynomial
open scoped Sym2
open N13TwoChartPicardRealization N13EffectiveInfinityRepair
open N13.TwoChartTensorCompatibility
/-- Degree-two divisors supported at the two actual infinity sections. -/
def infinityPairData (b c : Bool) : Data :=
  pointPairData (infinityLine b) (infinityLine c)
    (infinityPoint b) (infinityPoint c)
    (restrict_infinityLine b) (restrict_infinityLine c)
    ((if b then 1 else 0) + (if c then 1 else 0) - 2)
end
end MazurProof.N13EffectiveGraphData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveGraphData
noncomputable section
open Polynomial
open scoped Sym2
open N13TwoChartPicardRealization N13EffectiveInfinityRepair
open N13.TwoChartTensorCompatibility
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem infinityPairData_affineIdeal (b c : Bool) :
    (infinityPairData b c).charts.affineIdeal = ⊤ := by
  change (infinityLine b).affineIdeal * (infinityLine c).affineIdeal = ⊤
  rw [infinityLine_affineIdeal, infinityLine_affineIdeal, Ideal.top_mul]
end
end MazurProof.N13EffectiveGraphData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveGraphData
noncomputable section
open Polynomial
open scoped Sym2
open N13TwoChartPicardRealization N13EffectiveInfinityRepair
open N13.TwoChartTensorCompatibility
theorem infinityPairData_saturated (b c : Bool) :
    AffineVerticallySaturated (infinityPairData b c).charts :=
  affineVerticallySaturated_of_affineIdeal_eq_top _ (infinityPairData_affineIdeal b c)
end
end MazurProof.N13EffectiveGraphData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveGraphData
noncomputable section
open Polynomial
open scoped Sym2
open N13TwoChartPicardRealization N13EffectiveInfinityRepair
open N13.TwoChartTensorCompatibility
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem anchoredPointData_map_affineIdeal (x y : Q₂)
    (h : N13GoodModelTwo.AffineEquation x y) (b : Bool) :
    Ideal.map N13IntegralFractionalHull.integralToRational
        (anchoredPointData x y h b).charts.affineIdeal =
      SexticMumford.mumfordIdeal N13TwoChartPicardRealization.Model
        (X - C x) (C (N13EscapingDegreeOneSpread.pointY x y)) := by
  change Ideal.map N13IntegralFractionalHull.integralToRational
    ((N13QuadraticTwoChartSpread.pointLine x y h).affineIdeal *
      (infinityLine b).affineIdeal) = _
  rw [infinityLine_affineIdeal, Ideal.mul_top]
  exact N13QuadraticTwoChartSpread.map_pointLine_affineIdeal x y h
end
end MazurProof.N13EffectiveGraphData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveGraphData
noncomputable section
open Polynomial
open scoped Sym2
open N13TwoChartPicardRealization N13EffectiveInfinityRepair
open N13.TwoChartTensorCompatibility
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem anchoredPointData_saturated (x y : Q₂)
    (h : N13GoodModelTwo.AffineEquation x y) (b : Bool) :
    AffineVerticallySaturated (anchoredPointData x y h b).charts :=
  N13QuadraticTwoChartSpreadSaturation.affineVerticallySaturated_tensor _ _
    (N13QuadraticTwoChartSpreadSaturation.pointLine_affineVerticallySaturated x y h)
    (infinityLine_saturated b)
end
end MazurProof.N13EffectiveGraphData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveGraphData
noncomputable section
open Polynomial
open scoped Sym2
open N13TwoChartPicardRealization N13EffectiveInfinityRepair
open N13.TwoChartTensorCompatibility
def withMark (R : Data) (k : ℤ) : Data := { R with infinityOrder := k }
end
end MazurProof.N13EffectiveGraphData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveGraphData
noncomputable section
open Polynomial
open scoped Sym2
open N13TwoChartPicardRealization N13EffectiveInfinityRepair
open N13.TwoChartTensorCompatibility
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem raw_eq_of_map_and_mark
    (E : N13Mumford.SemiMumford Q₂) (R : Data)
    (hmap : Ideal.map N13IntegralFractionalHull.integralToRational R.charts.affineIdeal =
      SexticMumford.mumfordIdeal N13TwoChartPicardRealization.Model E.u E.v)
    (hmark : R.infinityOrder = E.nInf - 1) :
    genericRaw R.charts R.infinityOrder =
      SexticMumford.semiMumfordRaw N13TwoChartPicardRealization.Model E := by
  apply Prod.ext
  · change genericIdealUnit R.charts =
      SexticMumford.mumfordIdealUnit N13TwoChartPicardRealization.Model E
    apply Units.ext
    rw [coe_genericIdealUnit, SexticMumford.coe_mumfordIdealUnit]
    exact congrArg
      (fun I : Ideal N13IntegralFractionalHull.RationalRing =>
        (I : N13IntegralFractionalHull.RationalFractionalIdeal)) hmap
  · change Multiplicative.ofAdd R.infinityOrder = Multiplicative.ofAdd (E.nInf - 1)
    rw [hmark]
end
end MazurProof.N13EffectiveGraphData
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem branchZero_mem_xIdeal :
    branchZero ∈ xIdeal :=
  (Classical.choose_spec exists_branch_zero).2
end
end MazurProof.N13FormalInfinityBranches
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem branchZero_constantCoeff :
    PowerSeries.constantCoeff branchZero = 0 := by
  have hle :
      xIdeal ≤ RingHom.ker
        (PowerSeries.constantCoeff : Power →+* R₂) := by
    rw [xIdeal, Ideal.span_le]
    intro z hz
    subst z
    exact RingHom.mem_ker.mpr PowerSeries.constantCoeff_X
  exact RingHom.mem_ker.mp (hle branchZero_mem_xIdeal)
end
end MazurProof.N13FormalInfinityBranches
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem branchOne_constantCoeff :
    PowerSeries.constantCoeff branchOne = -1 := by
  simp [branchOne, branchZero_constantCoeff,
    N13FormalInfinityChart.hPower]
end
end MazurProof.N13FormalInfinityBranches
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchZero_of
    (f : Power) :
    evalBranchZero
        (AdjoinRoot.of
          N13FormalInfinityChart.infinityCurvePoly f) = f := by
  exact AdjoinRoot.lift_of eval₂_branchZero
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchOne_of
    (f : Power) :
    evalBranchOne
        (AdjoinRoot.of
          N13FormalInfinityChart.infinityCurvePoly f) = f := by
  exact AdjoinRoot.lift_of eval₂_branchOne
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchZero_vClass :
    evalBranchZero N13FormalInfinityChart.vClass =
      branchZero := by
  exact AdjoinRoot.lift_root eval₂_branchZero
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem evalBranchOne_vClass :
    evalBranchOne N13FormalInfinityChart.vClass =
      branchOne := by
  exact AdjoinRoot.lift_root eval₂_branchOne
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem hasInfinityMultiplicities_tensor
    (L M : Line) (p m q n : ℕ)
    (hL : HasInfinityMultiplicities L p m)
    (hM : HasInfinityMultiplicities M q n) :
    HasInfinityMultiplicities (N13TwoChartLineTensor.tensor L M) (p + q) (m + n) := by
  constructor
  · change Ideal.map positiveExpansion (L.infinityIdeal * M.infinityIdeal) = _
    rw [Ideal.map_mul, hL.1, hM.1, Ideal.span_singleton_mul_span_singleton, ← pow_add]
  · change Ideal.map negativeExpansion (L.infinityIdeal * M.infinityIdeal) = _
    rw [Ideal.map_mul, hL.2, hM.2, Ideal.span_singleton_mul_span_singleton, ← pow_add]
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem plus_ideal :
    N13TwoChartLineTensor.infinityPlusLine.infinityIdeal =
      Ideal.span ({N13IntegralInfinityChart.tClass, N13IntegralInfinityChart.vClass} : Set B) := by
  simp [N13TwoChartLineTensor.infinityPlusLine,
    N13TwoChartLineTensor.infinityPlusPoint, N13IntegralInfinityPointSpread.pointLine,
    N13IntegralInfinityPointSpread.pointIdeal, GeneralizedGraphIdealCore.graphIdeal,
    GeneralizedGraphIdealCore.ySubClass, N13IntegralInfinityPointSpread.pointU,
    N13IntegralInfinityPointSpread.pointV, N13IntegralInfinityPointSpread.yClass]
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
private theorem minus_ideal :
    N13TwoChartLineTensor.infinityMinusLine.infinityIdeal =
      Ideal.span ({N13IntegralInfinityChart.tClass, N13IntegralInfinityChart.vClass + 1} : Set B) := by
  simp [N13TwoChartLineTensor.infinityMinusLine,
    N13TwoChartLineTensor.infinityMinusPoint, N13IntegralInfinityPointSpread.pointLine,
    N13IntegralInfinityPointSpread.pointIdeal, GeneralizedGraphIdealCore.graphIdeal,
    GeneralizedGraphIdealCore.ySubClass, N13IntegralInfinityPointSpread.pointU,
    N13IntegralInfinityPointSpread.pointV, N13IntegralInfinityPointSpread.yClass]
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem positiveIntegralExpansion_t :
    positiveIntegralExpansion N13IntegralInfinityChart.tClass = PowerSeries.X := by
  simp [positiveIntegralExpansion]
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem negativeIntegralExpansion_t :
    negativeIntegralExpansion N13IntegralInfinityChart.tClass = PowerSeries.X := by
  simp [negativeIntegralExpansion]
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem positiveIntegralExpansion_v :
    positiveIntegralExpansion N13IntegralInfinityChart.vClass = N13FormalInfinityBranches.branchZero := by
  simp [positiveIntegralExpansion]
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem negativeIntegralExpansion_v :
    negativeIntegralExpansion N13IntegralInfinityChart.vClass = N13FormalInfinityBranches.branchOne := by
  simp [negativeIntegralExpansion]
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem integral_plus_on_plus :
    Ideal.map positiveIntegralExpansion N13TwoChartLineTensor.infinityPlusLine.infinityIdeal =
      Ideal.span ({PowerSeries.X} : Set P) := by
  rw [plus_ideal, Ideal.map_span, Set.image_pair,
    positiveIntegralExpansion_t, positiveIntegralExpansion_v]
  apply Ideal.span_pair_eq_span_left_iff_dvd.mpr
  exact PowerSeries.X_dvd_iff.mpr N13FormalInfinityBranches.branchZero_constantCoeff
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem integral_plus_on_minus :
    Ideal.map negativeIntegralExpansion N13TwoChartLineTensor.infinityPlusLine.infinityIdeal = ⊤ := by
  rw [plus_ideal, Ideal.map_span, Set.image_pair,
    negativeIntegralExpansion_t, negativeIntegralExpansion_v]
  apply span_pair_unit_right
  rw [PowerSeries.isUnit_iff_constantCoeff, N13FormalInfinityBranches.branchOne_constantCoeff]
  exact isUnit_neg_one
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem integral_minus_on_plus :
    Ideal.map positiveIntegralExpansion N13TwoChartLineTensor.infinityMinusLine.infinityIdeal = ⊤ := by
  rw [minus_ideal, Ideal.map_span, Set.image_pair,
    positiveIntegralExpansion_t, map_add, map_one, positiveIntegralExpansion_v]
  apply span_pair_unit_right
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simpa [N13FormalInfinityBranches.branchZero_constantCoeff] using (isUnit_one : IsUnit (1 : N13FormalInfinityChart.R₂))
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem integral_minus_on_minus :
    Ideal.map negativeIntegralExpansion N13TwoChartLineTensor.infinityMinusLine.infinityIdeal =
      Ideal.span ({PowerSeries.X} : Set P) := by
  rw [minus_ideal, Ideal.map_span, Set.image_pair,
    negativeIntegralExpansion_t, map_add, map_one, negativeIntegralExpansion_v]
  apply Ideal.span_pair_eq_span_left_iff_dvd.mpr
  apply PowerSeries.X_dvd_iff.mpr
  simp [N13FormalInfinityBranches.branchOne_constantCoeff]
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem infinityPlusLine_marked :
    HasInfinityMultiplicities N13TwoChartLineTensor.infinityPlusLine 1 0 := by
  constructor
  · exact generic_map_of_integral positiveIntegralExpansion _ 1
      (by simpa only [pow_one] using integral_plus_on_plus)
  · exact generic_map_of_integral negativeIntegralExpansion _ 0
      (by simpa only [pow_zero, Ideal.span_singleton_one] using integral_plus_on_minus)
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem infinityMinusLine_marked :
    HasInfinityMultiplicities N13TwoChartLineTensor.infinityMinusLine 0 1 := by
  constructor
  · exact generic_map_of_integral positiveIntegralExpansion _ 0
      (by simpa only [pow_zero, Ideal.span_singleton_one] using integral_minus_on_plus)
  · exact generic_map_of_integral negativeIntegralExpansion _ 1
      (by simpa only [pow_one] using integral_minus_on_minus)
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MarkedEffectiveData
noncomputable section
open Polynomial N13InfinityChartMarking
open N13TwoChartPicardRealization N13EffectiveInfinityRepair N13EffectiveGraphData
theorem infinityPairData_multiplicities (b c : Bool) :
    HasInfinityMultiplicities (infinityPairData b c).charts
      ((if b then 1 else 0) + (if c then 1 else 0))
      ((if b then 0 else 1) + (if c then 0 else 1)) := by
  cases b <;> cases c
  · exact hasInfinityMultiplicities_tensor _ _ 0 1 0 1
      infinityMinusLine_marked infinityMinusLine_marked
  · exact hasInfinityMultiplicities_tensor _ _ 0 1 1 0
      infinityMinusLine_marked infinityPlusLine_marked
  · exact hasInfinityMultiplicities_tensor _ _ 1 0 0 1
      infinityPlusLine_marked infinityMinusLine_marked
  · exact hasInfinityMultiplicities_tensor _ _ 1 0 1 0
      infinityPlusLine_marked infinityPlusLine_marked
end
end MazurProof.N13MarkedEffectiveData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MarkedEffectiveData
noncomputable section
open Polynomial N13InfinityChartMarking
open N13TwoChartPicardRealization N13EffectiveInfinityRepair N13EffectiveGraphData
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem exists_effective_data_marked
    (E : N13Mumford.SemiMumford Q₂) (hE : EffectiveChamber E) :
    ∃ R : Data, genericRaw R.charts R.infinityOrder =
        SexticMumford.semiMumfordRaw N13TwoChartPicardRealization.Model E ∧
      AffineVerticallySaturated R.charts ∧
      HasInfinityMultiplicities R.charts (positiveMultiplicity E) (negativeMultiplicity E) := by
  have hd := hE.1
  interval_cases he : E.u.natDegree
  · have hu : E.u = 1 := Polynomial.eq_one_of_monic_natDegree_zero E.u_monic he
    have hv : E.v = 0 := by
      have hh := E.v_reduced
      rw [hu] at hh
      simpa using hh.symm
    have hnlo := hE.2.1
    have hnhi : E.nInf ≤ 1 - (E.u.natDegree : ℤ) := by have := hE.2.2; omega
    rw [he] at hnhi
    norm_num at hnhi
    have hm (b c : Bool) :
        Ideal.map N13IntegralFractionalHull.integralToRational
            (infinityPairData b c).charts.affineIdeal =
          SexticMumford.mumfordIdeal N13TwoChartPicardRealization.Model E.u E.v := by
      rw [infinityPairData_affineIdeal, Ideal.map_top, hu, hv]
      exact (SexticMumford.zero_mumfordIdeal N13TwoChartPicardRealization.Model).symm
    interval_cases hn : E.nInf
    · refine ⟨infinityPairData false false, raw_eq_of_map_and_mark E _ (hm _ _) ?_,
        infinityPairData_saturated _ _, ?_⟩
      · change (-2 : ℤ) = E.nInf - 1
        omega
      · simpa [positiveMultiplicity, negativeMultiplicity, he, hn] using
          infinityPairData_multiplicities false false
    · refine ⟨infinityPairData false true, raw_eq_of_map_and_mark E _ (hm _ _) ?_,
        infinityPairData_saturated _ _, ?_⟩
      · change (-1 : ℤ) = E.nInf - 1
        omega
      · simpa [positiveMultiplicity, negativeMultiplicity, he, hn] using
          infinityPairData_multiplicities false true
    · refine ⟨infinityPairData true true, raw_eq_of_map_and_mark E _ (hm _ _) ?_,
        infinityPairData_saturated _ _, ?_⟩
      · change (0 : ℤ) = E.nInf - 1
        omega
      · simpa [positiveMultiplicity, negativeMultiplicity, he, hn] using
          infinityPairData_multiplicities true true
  · let D := balancedGraph E hE.1
    obtain ⟨x, y, hc, hD⟩ :=
      SexticMumford.exists_affinePoint_of_natDegree_eq_one
        N13TwoChartPicardRealization.Model D he rfl
    have hu : E.u = X - C x := congrArg (fun D => D.u) hD
    have hv : E.v = C y := congrArg (fun D => D.v) hD
    let hg := N13TwoChartLineTensor.goodY_onCurve x y hc
    have hm (b : Bool) :
        Ideal.map N13IntegralFractionalHull.integralToRational
            (anchoredPointData x (N13TwoChartLineTensor.goodY x y) hg b).charts.affineIdeal =
          SexticMumford.mumfordIdeal N13TwoChartPicardRealization.Model E.u E.v := by
      rw [anchoredPointData_map_affineIdeal, N13TwoChartLineTensor.pointY_goodY, hu, hv]
    have hnlo := hE.2.1
    have hnhi : E.nInf ≤ 1 - (E.u.natDegree : ℤ) := by have := hE.2.2; omega
    rw [he] at hnhi
    norm_num at hnhi
    interval_cases hn : E.nInf
    · refine ⟨anchoredPointData x (N13TwoChartLineTensor.goodY x y) hg false,
        raw_eq_of_map_and_mark E _ (hm _) ?_, anchoredPointData_saturated _ _ _ _, ?_⟩
      · change (-2 : ℤ) = E.nInf - 1
        omega
      · simpa [positiveMultiplicity, negativeMultiplicity, he, hn] using
          HuangN13.N13MarkedEffectiveData.anchoredPointData_multiplicities x (N13TwoChartLineTensor.goodY x y) hg false
    · refine ⟨anchoredPointData x (N13TwoChartLineTensor.goodY x y) hg true,
        raw_eq_of_map_and_mark E _ (hm _) ?_, anchoredPointData_saturated _ _ _ _, ?_⟩
      · change (-1 : ℤ) = E.nInf - 1
        omega
      · simpa [positiveMultiplicity, negativeMultiplicity, he, hn] using
          HuangN13.N13MarkedEffectiveData.anchoredPointData_multiplicities x (N13TwoChartLineTensor.goodY x y) hg true
  · let D := balancedGraph E hE.1
    obtain ⟨R, hraw, _, hs, hmarked⟩ := HuangN13.N13MarkedQuadraticExistence.exists_saturated_data D he
    have hm := map_affineIdeal_eq_of_genericRaw_eq_mumfordRaw R.charts R.infinityOrder D hraw
    refine ⟨withMark R (E.nInf - 1), raw_eq_of_map_and_mark E _ hm rfl, hs, ?_⟩
    have hn : E.nInf = -1 := by
      have hlo := hE.2.1
      have hhi := hE.2.2
      rw [he] at hhi
      omega
    simpa [positiveMultiplicity, negativeMultiplicity, withMark, he, hn] using hmarked
end
end MazurProof.N13MarkedEffectiveData
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem solution
    (E : MazurProof.N13Mumford.SemiMumford MazurProof.N13TwoChartPicardRealization.Q₂) (hE : MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E) :
    ∃ R : MazurProof.N13TwoChartPicardRealization.Data, MazurProof.N13TwoChartPicardRealization.genericRaw R.charts R.infinityOrder =
        MazurProof.SexticMumford.semiMumfordRaw MazurProof.N13TwoChartPicardRealization.Model E ∧
      MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities R.charts (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity E) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity E) := by
  exact MazurProof.N13MarkedEffectiveData.exists_effective_data_marked E hE
