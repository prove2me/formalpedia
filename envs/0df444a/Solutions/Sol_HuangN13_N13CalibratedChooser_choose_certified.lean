-- Prove2me | solution 1 for HuangN13.N13CalibratedChooser.choose_certified
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:01:00.563415+00:00
-- url     : https://prove2.me/submissions/2f372800-9ec1-4d4d-8fd5-e40ad7e90936

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SeparationDataCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore
import Theorems.Thm_HuangN13_N13EffectiveDataCompatibility_exists_certified_realization
import Theorems.Thm_HuangN13_N13QuadraticTwoChartSpread_pairLine_saturated_and_marked
import Theorems.Thm_MazurProof_N13IntegralInfinityPointSpread_pointIdeal_isUnit

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
      a * (X - _root_.Polynomial.C x₁) + b * (X - _root_.Polynomial.C x₂) = 1 := by
  have hd : x₂ - x₁ ≠ 0 :=
    sub_ne_zero.mpr hneq.symm
  refine
    ⟨_root_.Polynomial.C ((x₂ - x₁)⁻¹), -_root_.Polynomial.C ((x₂ - x₁)⁻¹), ?_⟩
  calc
    _root_.Polynomial.C ((x₂ - x₁)⁻¹) * (X - _root_.Polynomial.C x₁) +
          -_root_.Polynomial.C ((x₂ - x₁)⁻¹) * (X - _root_.Polynomial.C x₂) =
        _root_.Polynomial.C ((x₂ - x₁)⁻¹) * _root_.Polynomial.C (x₂ - x₁) := by
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
          (X - _root_.Polynomial.C x₁) (_root_.Polynomial.C z₁) *
        SexticMumford.mumfordIdeal
          N13EscapingDegreeOneSpread.Model
          (X - _root_.Polynomial.C x₂) (_root_.Polynomial.C z₂) =
      SexticMumford.mumfordIdeal
        N13EscapingDegreeOneSpread.Model
        ((X - _root_.Polynomial.C x₁) * (X - _root_.Polynomial.C x₂))
        (secantV x₁ z₁ x₂ z₂) := by
  have h₁ :
      X - _root_.Polynomial.C x₁ ∣ secantV x₁ z₁ x₂ z₂ - _root_.Polynomial.C z₁ := by
    simpa using
      (X_sub_C_dvd_sub_C_eval
        (p := secantV x₁ z₁ x₂ z₂) (a := x₁))
  have h₂ :
      X - _root_.Polynomial.C x₂ ∣ secantV x₁ z₁ x₂ z₂ - _root_.Polynomial.C z₂ := by
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
        (X - _root_.Polynomial.C x₁) (X - _root_.Polynomial.C x₂) (_root_.Polynomial.C z₁) (_root_.Polynomial.C z₂)
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
/-- A split balanced quadratic Mumford graph is literally the product of
the two point ideals, not only equal to it in the Picard quotient. -/
theorem mumfordIdeal_eq_pointIdeal_mul_of_split
    (D : SexticMumford.Mumford
      N13EscapingDegreeOneSpread.Model)
    (hdeg : D.u.natDegree = 2)
    (x₁ x₂ : N13EscapingDegreeOneSpread.Q₂)
    (hfactor :
      D.u = (X - _root_.Polynomial.C x₁) * (X - _root_.Polynomial.C x₂))
    (hneq : x₁ ≠ x₂) :
    SexticMumford.mumfordIdeal
          N13EscapingDegreeOneSpread.Model
          (X - _root_.Polynomial.C x₁) (_root_.Polynomial.C (D.v.eval x₁)) *
        SexticMumford.mumfordIdeal
          N13EscapingDegreeOneSpread.Model
          (X - _root_.Polynomial.C x₂) (_root_.Polynomial.C (D.v.eval x₂)) =
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
        (X - _root_.Polynomial.C x)
        (_root_.Polynomial.C (N13EscapingDegreeOneSpread.pointY x y)) := by
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
        (X - _root_.Polynomial.C x)
        (_root_.Polynomial.C (N13EscapingDegreeOneSpread.pointY x y)) := by
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
        (X - _root_.Polynomial.C x)
        (_root_.Polynomial.C (N13EscapingDegreeOneSpread.pointY x y)) := by
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
          (X - _root_.Polynomial.C x₁)
          (_root_.Polynomial.C (N13EscapingDegreeOneSpread.pointY x₁ y₁)) *
        SexticMumford.mumfordIdeal Model
          (X - _root_.Polynomial.C x₂)
          (_root_.Polynomial.C (N13EscapingDegreeOneSpread.pointY x₂ y₂)) := by
  rw [pairLine, N13TwoChartLineTensor.map_tensor_affineIdeal,
    map_pointLine_affineIdeal, map_pointLine_affineIdeal]
end
end MazurProof.N13QuadraticTwoChartSpread
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The doubled positive-infinity line is vertically saturated on the
affine chart.  Both point factors are trivial there, so their tensor product
has the unit ideal and contains no vertical torsion. -/
theorem infinityPlusLine_affineVerticallySaturated :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      infinityPlusLine := by
  apply
    N13TwoChartPicardRealization.affineVerticallySaturated_of_affineIdeal_eq_top
  simp [infinityPlusLine]
end
end MazurProof.N13InfinityPointPicardRealization
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13InfinityPointPicardRealization
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The anchored negative-infinity line is vertically saturated on the
affine chart.  As for the positive branch, all geometric information lives
on the infinity chart and the affine ideal is the unit ideal. -/
theorem infinityMinusLine_affineVerticallySaturated :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      infinityMinusLine := by
  apply
    N13TwoChartPicardRealization.affineVerticallySaturated_of_affineIdeal_eq_top
  simp [infinityMinusLine]
end
end MazurProof.N13InfinityPointPicardRealization
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
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace MazurProof.N13InverseInfinityWitness
open Polynomial MazurProof.N13Arithmetic
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The witness's affine lattice is vertically saturated (pair line certificate). -/
theorem inverseInfinityData_affineVerticallySaturated :
    N13TwoChartPicardRealization.AffineVerticallySaturated inverseInfinityData.charts :=
  (HuangN13.N13QuadraticTwoChartSpread.pairLine_saturated_and_marked).1
    (0 : N13SplitQuadraticSpecialRestriction.Q₂) (N13TwoChartLineTensor.goodY 0 1)
    (-1) (N13TwoChartLineTensor.goodY (-1) 1)
    MazurProof.N13InverseInfinityData.curve_zero MazurProof.N13InverseInfinityData.curve_negOne
end MazurProof.N13InverseInfinityWitness
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
namespace MazurProof.N13EffectiveDataCompatibility
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13InfinityChartMarking hiding Line B QP
open N13EffectiveInfinityRepair hiding Model
open N13MarkedTensorComparison
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem chooseUncalibrated_certified (P : G) : Certified (chooseUncalibrated P) :=
  (Classical.choose_spec (HuangN13.N13EffectiveDataCompatibility.exists_certified_realization P)).1
end
end MazurProof.N13EffectiveDataCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PointDataCertificates
noncomputable section
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking hiding Line B QP
open N13TwoChartPicardRealization
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem infinityPlus_certified : Certified N13InfinityPointPicardRealization.infinityPlusData := by
  refine ⟨(SexticMumford.zero Model).toSemi, ?_, ?_,
    N13InfinityPointPicardRealization.infinityPlusLine_affineVerticallySaturated, ?_⟩
  · norm_num [EffectiveChamber, SexticMumford.zero]
  · exact genericRaw_eq_mumfordRaw_of_map_affineIdeal_eq _ _
      N13InfinityPointPicardRealization.map_infinityPlusLine_affineIdeal
  · have h := hasInfinityMultiplicities_tensor _ _ 1 0 1 0 infinityPlusLine_marked infinityPlusLine_marked
    convert h using 2 <;>
      first | rfl | simp [positiveMultiplicity, negativeMultiplicity, SexticMumford.zero]
end
end MazurProof.N13PointDataCertificates
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PointDataCertificates
noncomputable section
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking hiding Line B QP
open N13TwoChartPicardRealization
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem infinityMinus_certified : Certified N13InfinityPointPicardRealization.infinityMinusData := by
  refine ⟨(SexticMumford.infinityMinusMumford Model).toSemi, ?_, ?_,
    N13InfinityPointPicardRealization.infinityMinusLine_affineVerticallySaturated, ?_⟩
  · norm_num [EffectiveChamber, SexticMumford.infinityMinusMumford]
  · exact genericRaw_eq_mumfordRaw_of_map_affineIdeal_eq _ _
      N13InfinityPointPicardRealization.map_infinityMinusLine_affineIdeal
  · have h := hasInfinityMultiplicities_tensor _ _ 0 1 1 0 infinityMinusLine_marked infinityPlusLine_marked
    convert h using 2 <;>
      first | rfl | simp [positiveMultiplicity, negativeMultiplicity, SexticMumford.infinityMinusMumford]
end
end MazurProof.N13PointDataCertificates
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CalibratedChooser
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking N13TwoChartPicardRealization N13PointDataCertificates
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem caLine_map :
    Ideal.map N13IntegralFractionalHull.integralToRational
        N13InverseInfinityWitness.caLine.affineIdeal =
      SexticMumford.mumfordIdeal Model caSemi.u caSemi.v := by
  change Ideal.map N13TwoAdicCoordinateBaseChange.integralToSextic
    (N13QuadraticTwoChartSpread.pairLine _ _ _ _ _ _).affineIdeal = _
  rw [N13QuadraticTwoChartSpread.map_pairLine_affineIdeal,
    N13TwoChartLineTensor.pointY_goodY, N13TwoChartLineTensor.pointY_goodY]
  simpa [caMumford, caSemi] using
    N13TwoChartLineTensor.mumfordIdeal_eq_pointIdeal_mul_of_split
      caMumford ca_degree (0 : Q₂) (-1) (by simp [caMumford]) (by norm_num)
end
end MazurProof.N13CalibratedChooser
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CalibratedChooser
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking N13TwoChartPicardRealization N13PointDataCertificates
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
set_option maxHeartbeats 800000 in
theorem inverseInfinity_certified : Certified N13InverseInfinityWitness.inverseInfinityData := by
  have hd : caSemi.u.natDegree = 2 := ca_degree
  have hn : caSemi.nInf = -1 := rfl
  refine ⟨caSemi, ?_, ?_,
    N13InverseInfinityWitness.inverseInfinityData_affineVerticallySaturated, ?_⟩
  · simp [EffectiveChamber, hd, hn]
  · exact N13EffectiveGraphData.raw_eq_of_map_and_mark caSemi
      N13InverseInfinityWitness.inverseInfinityData caLine_map
      (by show (-2 : ℤ) = -1 - 1; norm_num)
  · have hm := (HuangN13.N13QuadraticTwoChartSpread.pairLine_saturated_and_marked).2 (0 : Q₂) (N13TwoChartLineTensor.goodY 0 1)
        (-1) (N13TwoChartLineTensor.goodY (-1) 1)
        N13InverseInfinityData.curve_zero N13InverseInfinityData.curve_negOne
    have hp : positiveMultiplicity caSemi = 0 := by
      simp [positiveMultiplicity, hn]
    have hq : negativeMultiplicity caSemi = 0 := by
      simp [negativeMultiplicity, hd, hn]
    rw [hp, hq]
    change HasInfinityMultiplicities N13InverseInfinityWitness.caLine 0 0
    exact hm
end
end MazurProof.N13CalibratedChooser
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CalibratedChooser
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking N13TwoChartPicardRealization N13PointDataCertificates
theorem choose_certified (P : G) : Certified (choose P) := by
  unfold choose
  split
  · exact infinityPlus_certified
  · split
    · exact infinityMinus_certified
    · split
      · exact inverseInfinity_certified
      · exact chooseUncalibrated_certified P
end
end MazurProof.N13CalibratedChooser
end
end


set_option autoImplicit false
open Polynomial
theorem solution (P : MazurProof.N13EffectiveDataCompatibility.G) : MazurProof.N13EffectiveDataCompatibility.Certified (MazurProof.N13CalibratedChooser.choose P) := by
  exact MazurProof.N13CalibratedChooser.choose_certified P
