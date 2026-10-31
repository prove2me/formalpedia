-- Prove2me | solution 1 for HuangN13.N13ConstructedMappedSpecialFamily.representative_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:39:56.880003+00:00
-- url     : https://prove2.me/submissions/0a8471da-ae25-497a-932b-395b57db8897

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_CompatibleReductionCore
import Definitions.Def_HuangN13_DoublingStatementCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SeparationDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore
import Theorems.Thm_HuangN13_N13CalibratedChooser_choose_generic
import Theorems.Thm_HuangN13_N13ConstructedSpecialization_chosen_point_specialClass
import Theorems.Thm_HuangN13_N13KernelInfinityMultiplicity_chosen_translated_finite_graph
import Theorems.Thm_MazurProof_N13GoodSexticMumfordTransport_sextic_mumfordIdeal_eq_of_dvd_sub
import Theorems.Thm_MazurProof_N13ProperCurveReduction_reduceCurve_cusp

set_option autoImplicit false

namespace MazurProof.N13SpecialDegreeFourCode
end MazurProof.N13SpecialDegreeFourCode
section
section
set_option autoImplicit false
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.N13GoodCoordinateRingTwo
noncomputable section
@[simp] theorem xClass_add (p q : K[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q
end
end MazurProof.N13GoodCoordinateRingTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13TwoAdicDisks
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicDisks.instFactPrimeOfNatNat_fLT
theorem y_eq_zeroDiskY
    (x : R₂) (hx : x ∈ maximal)
    {y : R₂}
    (hy : N13GoodModelTwo.AffineEquation x y)
    (hymem : y ∈ maximal) :
    y = zeroDiskY x hx :=
  y_eq_of_mem_maximal x y (zeroDiskY x hx)
    (h_isUnit_of_mem_zeroDisk hx)
    hy (zeroDiskY_spec x hx).1 hymem
    (zeroDiskY_spec x hx).2
end
end MazurProof.N13TwoAdicDisks
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13TwoAdicDisks
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicDisks.instFactPrimeOfNatNat_fLT
@[simp] theorem zeroDiskY_zero :
    zeroDiskY 0 maximal.zero_mem = 0 := by
  symm
  apply y_eq_zeroDiskY 0 maximal.zero_mem
  · simp [N13GoodModelTwo.AffineEquation,
      N13GoodModelTwo.h, N13GoodModelTwo.rhs]
  · exact maximal.zero_mem
end
end MazurProof.N13TwoAdicDisks
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13TwoAdicDisks
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicDisks.instFactPrimeOfNatNat_fLT
theorem y_eq_negOneDiskY
    (x : R₂) (hx : x + 1 ∈ maximal)
    {y : R₂}
    (hy : N13GoodModelTwo.AffineEquation x y)
    (hymem : y ∈ maximal) :
    y = negOneDiskY x hx :=
  y_eq_of_mem_maximal x y (negOneDiskY x hx)
    (h_isUnit_of_mem_negOneDisk hx)
    hy (negOneDiskY_spec x hx).1 hymem
    (negOneDiskY_spec x hx).2
end
end MazurProof.N13TwoAdicDisks
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13TwoAdicDisks
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicDisks.instFactPrimeOfNatNat_fLT
@[simp] theorem negOneDiskY_negOne :
    negOneDiskY (-1) (by simp) = 0 := by
  symm
  apply y_eq_negOneDiskY (-1) (by simp)
  · simp [N13GoodModelTwo.AffineEquation,
      N13GoodModelTwo.h, N13GoodModelTwo.rhs]
    ring
  · exact maximal.zero_mem
end
end MazurProof.N13TwoAdicDisks
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13TwoAdicAbelChartData
noncomputable section
namespace DiskPair
variable (P : DiskPair)
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
@[simp] theorem basePair_y₀ :
    basePair.y₀ = 0 :=
  N13TwoAdicDisks.zeroDiskY_zero
end DiskPair
end
end MazurProof.N13TwoAdicAbelChartData
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13TwoAdicAbelChartData
noncomputable section
namespace DiskPair
variable (P : DiskPair)
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
@[simp] theorem basePair_y₁ :
    basePair.y₁ = 0 :=
  N13TwoAdicDisks.negOneDiskY_negOne
end DiskPair
end
end MazurProof.N13TwoAdicAbelChartData
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13TwoAdicAbelChartData
noncomputable section
namespace DiskPair
variable (P : DiskPair)
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
@[simp] theorem basePair_u :
    basePair.u =
      N13FormalAbelLinearization.uBase := by
  simp [u, basePair, N13FormalAbelLinearization.uBase]
  ring
end DiskPair
end
end MazurProof.N13TwoAdicAbelChartData
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13TwoAdicAbelChartData
noncomputable section
namespace DiskPair
variable (P : DiskPair)
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
@[simp] theorem basePair_v :
    basePair.v = 0 := by
  change basePair.interpolate basePair.y₀ basePair.y₁ = 0
  rw [basePair_y₀, basePair_y₁]
  simp [interpolate]
end DiskPair
end
end MazurProof.N13TwoAdicAbelChartData
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
namespace MazurProof.N13CalibratedChooser
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking N13TwoChartPicardRealization N13PointDataCertificates
@[simp] theorem choose_zero : choose 0 = N13InfinityPointPicardRealization.infinityPlusData := by
  simp [choose]
end
end MazurProof.N13CalibratedChooser
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
@[simp] theorem divisorCode_mk
    (P Q : N13AbelFiberTwoModel.CurvePoint) :
    divisorCode s(P, Q) = pointCode P + pointCode Q := by
  rfl
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
theorem pointCode_eq_codeBP (P : N13AbelFiberTwoModel.CurvePoint) :
    pointCode P = codeBP (curvePointEquiv P) := by
  rfl
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
open scoped Sym2
open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo
namespace MazurProof.N13SpecialAbelCode
noncomputable section
@[simp] theorem picCode_abel (D : EffectiveDivisorTwo) :
    picCode (abel D) = divisorCode D :=
  rfl
end
end MazurProof.N13SpecialAbelCode
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13.SpecialCuspCodeChecks
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction
/-- The sheet at x = 1 is reversed by the good-model coordinate change. -/
theorem pointCode_cusp (c : N13Mumford.Cusp13) :
    pointCode (specialCuspEquiv c) =
      match c with
      | .infinityPlus => 8
      | .infinityMinus => -8
      | .zeroPlus => 1
      | .zeroMinus => -1
      | .negOnePlus => -7
      | .negOneMinus => 7 := by
  rw [pointCode_eq_codeBP, curvePointEquiv_specialCuspEquiv]
  cases c <;> norm_num [codeBP, cuspCoordinate, baseAmplitude]
end
end MazurProof.N13.SpecialCuspCodeChecks
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13.SpecialCuspCodeChecks
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction
/-- The raw code of the doubled positive anchor is 16. -/
theorem divisorCode_double_anchor :
    divisorCode s(specialCuspEquiv .infinityPlus,
      specialCuspEquiv .infinityPlus) = 16 := by
  rw [divisorCode_mk, pointCode_cusp]
  norm_num
end
end MazurProof.N13.SpecialCuspCodeChecks
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedSpecialization
noncomputable section
open N13SpecialDivisorCharts N13CoherentChartComparison
open N13SpecialAbelCode hiding EffectiveDivisorTwo
open N13SpecialDegreeFourCode
theorem chosen_zero_specialClass : (N13CalibratedChooser.choose 0).toSpecialPic =
    N13RationalPointEndgame.specialPointClass N13RationalPointEndgame.specialAnchor := by
  rw [N13CalibratedChooser.choose_zero, N13InfinityPointPicardRealization.infinityPlusData_toSpecialPic,
    N13InfinityLineSpecialRestriction.specialInfinityPlusPoint_eq_specialAnchor]
end
end MazurProof.N13ConstructedSpecialization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedSpecialization
noncomputable section
open N13SpecialDivisorCharts N13CoherentChartComparison
open N13SpecialAbelCode hiding EffectiveDivisorTwo
open N13SpecialDegreeFourCode
/-- Pointwise compatibility with the actual proper reduction, recentered at
the same positive infinity anchor used by the rational Abel map. -/
theorem specialization_rationalAbel (P : N13RationalPointEndgame.RationalCurvePoint) :
    specialization (N13RationalPointEndgame.rationalAbel P) =
      pointCode (N13ProperCurveReduction.reduceCurve P) - pointCode N13RationalPointEndgame.specialAnchor := by
  change divisorCode (chosenDivisor (N13RationalPointEndgame.rationalAbel P)) -
      divisorCode (chosenDivisor 0) = _
  change picCode (N13CalibratedChooser.choose (N13RationalPointEndgame.rationalAbel P)).toSpecialPic -
      picCode (N13CalibratedChooser.choose 0).toSpecialPic = _
  rw [HuangN13.N13ConstructedSpecialization.chosen_point_specialClass, chosen_zero_specialClass]
  change divisorCode _ - divisorCode _ = _
  simp only [N13RationalPointEndgame.specialPointClass, picCode_abel, divisorCode_mk]
  ring
end
end MazurProof.N13ConstructedSpecialization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBaseDivisor
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization
theorem baseDivisor_code : divisorCode baseDivisor = 8 := by
  rw [baseDivisor, divisorCode_mk,
    N13.SpecialCuspCodeChecks.pointCode_cusp,
    N13.SpecialCuspCodeChecks.pointCode_cusp]
  decide
end
end MazurProof.N13KernelBaseDivisor
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBaseDivisor
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization
theorem baseDivisor_not_canonical :
    ¬ N13AbelFiberTwoModel.IsCanonical baseDivisor := by
  rintro ⟨b, hb⟩
  have hz : divisorCode baseDivisor = 0 := by
    rw [← hb, divisorCode_canonicalDivisor]
  rw [baseDivisor_code] at hz
  exact (by decide : (8 : ZMod 19) ≠ 0) hz
end
end MazurProof.N13KernelBaseDivisor
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBaseDivisor
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization
theorem divisor_eq_base_of_code (D : EffectiveDivisorTwo)
    (h : divisorCode D = 8) : D = baseDivisor := by
  have he := (divisorCode_eq_iff_abelRel D baseDivisor).mp
    (h.trans baseDivisor_code.symm)
  rcases he with he | ⟨_, hb⟩
  · exact he
  · exact (baseDivisor_not_canonical hb).elim
end
end MazurProof.N13KernelBaseDivisor
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBaseDivisor
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization
theorem chosen_zero_code : divisorCode (chosenDivisor 0) = 16 := by
  have h := congrArg picCode chosen_zero_specialClass
  change divisorCode (chosenDivisor 0) =
    divisorCode s(N13RationalPointEndgame.specialAnchor,
      N13RationalPointEndgame.specialAnchor) at h
  exact h.trans N13.SpecialCuspCodeChecks.divisorCode_double_anchor
end
end MazurProof.N13KernelBaseDivisor
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBaseDivisor
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization
theorem specialization_cusp (c : N13Mumford.Cusp13) :
    specialization (N13RationalPointEndgame.rationalAbel (N13Mumford.cuspPoint c)) =
      pointCode (specialCuspEquiv c) - 8 := by
  rw [specialization_rationalAbel, N13ProperCurveReduction.reduceCurve_cusp]
  change pointCode (specialCuspEquiv c) -
    pointCode (specialCuspEquiv .infinityPlus) = _
  rw [N13.SpecialCuspCodeChecks.pointCode_cusp .infinityPlus]
end
end MazurProof.N13KernelBaseDivisor
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBaseDivisor
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization
theorem specialization_baseTranslate : specialization baseTranslate = 8 - 16 := by
  rw [baseTranslate, map_add, specialization_cusp, specialization_cusp,
    N13.SpecialCuspCodeChecks.pointCode_cusp,
    N13.SpecialCuspCodeChecks.pointCode_cusp]
  decide
end
end MazurProof.N13KernelBaseDivisor
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBaseDivisor
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization
theorem chosen_translated_code (z : Kernel) :
    divisorCode (chosenDivisor ((z : G) + baseTranslate)) = 8 := by
  have hz : specialization (z : G) = 0 := z.property
  have ht : specialization ((z : G) + baseTranslate) = 8 - 16 := by
    rw [map_add, hz, zero_add, specialization_baseTranslate]
  change divisorCode (chosenDivisor ((z : G) + baseTranslate)) -
    divisorCode (chosenDivisor 0) = 8 - 16 at ht
  rw [chosen_zero_code] at ht
  exact sub_left_injective ht
end
end MazurProof.N13KernelBaseDivisor
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBaseDivisor
noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization
/-- The literal special divisor of the same chosen geometric witness. -/
theorem chosen_translated_divisor (z : Kernel) :
    (N13CalibratedChooser.choose ((z : G) + baseTranslate)).specialDivisor =
      baseDivisor :=
  divisor_eq_base_of_code _ (chosen_translated_code z)
end
end MazurProof.N13KernelBaseDivisor
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelGraphContraction
noncomputable section
open Polynomial N13KernelBaseDivisor N13KernelInfinityMultiplicity
open N13TwoChartPicardRealization N13EffectiveGraphData N13EffectiveInfinityRepair
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13KernelGraphContraction.instFactPrimeOfNatNat_fLT
theorem baseDivisor_affineIdeal :
    (N13SpecialDivisorCharts.ofDivisor baseDivisor).affineIdeal =
      N13SpecialQuotientBasis.specialIdeal := by
  change N13GoodCoordinateRingTwo.mumfordIdeal (X - _root_.Polynomial.C 0) (_root_.Polynomial.C 0) *
    N13GoodCoordinateRingTwo.mumfordIdeal (X - _root_.Polynomial.C 1) (_root_.Polynomial.C 0) = _
  simp only [C_0, C_1, sub_zero]
  have hm := GeneralizedGraphIdealCore.graphIdeal_mul_of_coprime
    N13GoodCoordinateRingTwo.xClassHom N13GoodCoordinateRingTwo.yClass
    X (X - 1) 0 0 0 (by simp) (by simp)
    (show ∃ a b : (ZMod 2)[X], a * X + b * (X - 1) = 1 from
      ⟨1, -1, by ring⟩)
  have hp : (X : (ZMod 2)[X]) * (X - 1) = X ^ 2 + X := by
    have hn : (-1 : (ZMod 2)[X]) = 1 := CharTwo.neg_eq 1
    rw [sub_eq_add_neg, hn]
    ring
  simpa [N13GoodCoordinateRingTwo.mumfordIdeal,
    GeneralizedGraphIdealCore.graphIdeal, GeneralizedGraphIdealCore.ySubClass,
    N13GoodCoordinateRingTwo.ySubClass,
    N13SpecialQuotientBasis.specialIdeal, hp] using hm
end
end MazurProof.N13KernelGraphContraction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelGraphContraction
noncomputable section
open Polynomial N13KernelBaseDivisor N13KernelInfinityMultiplicity
open N13TwoChartPicardRealization N13EffectiveGraphData N13EffectiveInfinityRepair
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13KernelGraphContraction.instAlgebraAR MazurProof.N13KernelGraphContraction.instIsLocalizationIntegralRingVerticalScalarsR
theorem contract_map_eq_of_saturated (L : Line) (hs : AffineVerticallySaturated L) :
    N13IntegralModelContraction.contractIdeal
      (Ideal.map N13IntegralFractionalHull.integralToRational L.affineIdeal) =
        L.affineIdeal := by
  apply le_antisymm
  · intro a ha
    change algebraMap A R a ∈ Ideal.map (algebraMap A R) L.affineIdeal at ha
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
      N13IntegralModelContraction.verticalScalars] at ha
    obtain ⟨q, hq, hqa⟩ := ha
    obtain ⟨r, hr, hqr⟩ := hq
    rw [← hqr] at hqa
    exact hs r (mem_nonZeroDivisors_iff_ne_zero.mp hr) a hqa
  · intro a ha
    exact Ideal.mem_map_of_mem (algebraMap A R) ha
end
end MazurProof.N13KernelGraphContraction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelGraphContraction
noncomputable section
open Polynomial N13KernelBaseDivisor N13KernelInfinityMultiplicity
open N13TwoChartPicardRealization N13EffectiveGraphData N13EffectiveInfinityRepair
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem map_affineIdeal_of_semiRaw
    (D : Data) (E : N13Mumford.SemiMumford Q₂)
    (hr : genericRaw D.charts D.infinityOrder = SexticMumford.semiMumfordRaw Model E) :
    Ideal.map N13IntegralFractionalHull.integralToRational D.charts.affineIdeal =
      SexticMumford.mumfordIdeal Model E.u E.v := by
  have hu := congrArg Prod.fst hr
  have hf := congrArg (fun U : Units N13IntegralFractionalHull.RationalFractionalIdeal =>
    (U : N13IntegralFractionalHull.RationalFractionalIdeal)) hu
  change (genericIdealUnit D.charts : N13IntegralFractionalHull.RationalFractionalIdeal) =
    (SexticMumford.mumfordIdealUnit Model E :
      N13IntegralFractionalHull.RationalFractionalIdeal) at hf
  rw [coe_genericIdealUnit, SexticMumford.coe_mumfordIdealUnit] at hf
  exact FractionalIdeal.coeIdeal_injective hf
end
end MazurProof.N13KernelGraphContraction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelGraphContraction
noncomputable section
open Polynomial N13KernelBaseDivisor N13KernelInfinityMultiplicity
open N13TwoChartPicardRealization N13EffectiveGraphData N13EffectiveInfinityRepair
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The balanced graph has the exact required contracted special ideal.
Its class still needs the separately proved mark-shift identity. -/
theorem balancedGraph_map_contract
    (D : Data) (E : N13Mumford.SemiMumford Q₂) (hd : E.u.natDegree ≤ 2)
    (hr : genericRaw D.charts D.infinityOrder = SexticMumford.semiMumfordRaw Model E)
    (hsat : AffineVerticallySaturated D.charts)
    (hspecial : D.specialDivisor = baseDivisor) :
    Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
      (N13IntegralModelContraction.contractIdeal
        (N13CanonicalContractionQuotient.graphIdeal (balancedGraph E hd).toSemi)) =
      N13SpecialQuotientBasis.specialIdeal := by
  change Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
    (N13IntegralModelContraction.contractIdeal
      (SexticMumford.mumfordIdeal Model E.u E.v)) = _
  rw [← map_affineIdeal_of_semiRaw D E hr, contract_map_eq_of_saturated D.charts hsat]
  have h := D.special_affine
  rw [hspecial] at h
  exact h.trans baseDivisor_affineIdeal
end
end MazurProof.N13KernelGraphContraction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBasePic
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13KernelBaseDivisor N13KernelGraphContraction
open N13TwoChartPicardRealization N13EffectiveGraphData
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem rawClass_mul (r s : SexticMumford.OrientedFrac Model) :
    rawClass (r * s) = rawClass r + rawClass s := by
  unfold rawClass
  rw [map_mul]
  rfl
end
end MazurProof.N13KernelBasePic
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBasePic
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13KernelBaseDivisor N13KernelGraphContraction
open N13TwoChartPicardRealization N13EffectiveGraphData
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem balancedGraph_class (D : Data) (E : N13Mumford.SemiMumford Q₂)
    (hd : E.u.natDegree ≤ 2) (hn : E.nInf = -1)
    (hr : genericRaw D.charts D.infinityOrder = SexticMumford.semiMumfordRaw Model E) :
    SexticMumford.classOf Model (N13Infinity.positiveInfinityOrder Q₂)
      (balancedGraph E hd) = D.toGenericPic + infinityShift := by
  have hraw : SexticMumford.mumfordRaw Model (balancedGraph E hd) =
      genericRaw D.charts D.infinityOrder * (1, Multiplicative.ofAdd 1) := by
    rw [hr]
    apply Prod.ext
    · change SexticMumford.mumfordIdealUnit Model (balancedGraph E hd).toSemi =
        SexticMumford.mumfordIdealUnit Model E * 1
      rw [mul_one]
      apply Units.ext
      simp only [SexticMumford.coe_mumfordIdealUnit]
      rfl
    · change Multiplicative.ofAdd (-1 : ℤ) = Multiplicative.ofAdd (E.nInf - 1 + 1)
      rw [hn]
      rfl
  change rawClass _ = rawClass _ + rawClass _
  rw [hraw, rawClass_mul]
end
end MazurProof.N13KernelBasePic
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBasePic
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13KernelBaseDivisor N13KernelGraphContraction
open N13TwoChartPicardRealization N13EffectiveGraphData
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem basePair_graphIdeal :
    SexticMumford.mumfordIdeal Model basePair.mumford.u basePair.mumford.v =
      SexticMumford.mumfordIdeal Model (X * (X + 1)) (2 * X + 1) := by
  have hu : basePair.mumford.u = X * (X + 1) := by
    simp [N13TwoAdicAbelChartPic.DiskPair.mumford_u,
      N13TwoAdicMumfordTransport.mapPoly, N13FormalAbelLinearization.uBase]
    ring
  have hv : basePair.mumford.v =
      N13GoodSexticMumfordTransport.reducedCompletedGraph (X * (X + 1)) 0 := by
    rw [N13TwoAdicAbelChartPic.DiskPair.mumford_v,
      N13TwoAdicMumfordTransport.sexticSemi_v,
      N13TwoAdicAbelChartData.DiskPair.smoothMumford_u,
      N13TwoAdicAbelChartData.DiskPair.smoothMumford_v,
      N13TwoAdicAbelChartData.DiskPair.basePair_v, map_zero]
    congr 1
  rw [hu, hv]
  rw [← N13GoodSexticMumfordTransport.map_mumfordIdeal_reduced,
    N13GoodSexticMumfordTransport.map_mumfordIdeal]
  apply N13GoodSexticMumfordTransport.sextic_mumfordIdeal_eq_of_dvd_sub
  refine ⟨X - 1, ?_⟩
  simp only [N13GoodSexticMumfordTransport.completedGraph, mul_zero, zero_add,
    N13GeneralizedMumfordIntegral.hPoly]
  ring
end
end MazurProof.N13KernelBasePic
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBasePic
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13KernelBaseDivisor N13KernelGraphContraction
open N13TwoChartPicardRealization N13EffectiveGraphData
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
private theorem cuspMumford_class (c : N13Mumford.Cusp13) :
    SexticMumford.classOf Model (N13Infinity.positiveInfinityOrder Q₂) (cuspMumford c) =
      N13InfinityBaseChange.picMapRatToQ₂
        (N13RationalPointEndgame.rationalAbel (N13Mumford.cuspPoint c)) := by
  exact (N13InfinityBaseChange.picMapRatToQ₂_classOf _).symm
end
end MazurProof.N13KernelBasePic
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13KernelBasePic
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13KernelBaseDivisor N13KernelGraphContraction
open N13TwoChartPicardRealization N13EffectiveGraphData
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem basePic_eq_translated_twist :
    N13RationalKernelDoublingAdapter.basePic =
      N13InfinityBaseChange.picMapRatToQ₂ baseTranslate + infinityShift := by
  let C := cuspMumford .zeroPlus
  let B := cuspMumford .negOneMinus
  have hpair : SexticMumford.mumfordIdeal Model C.u C.v *
      SexticMumford.mumfordIdeal Model B.u B.v =
        SexticMumford.mumfordIdeal Model basePair.mumford.u basePair.mumford.v := by
    rw [basePair_graphIdeal]
    have h := N13TwoChartLineTensor.pointIdeal_mul_eq_secantGraph
      (0 : Q₂) 1 (-1) (-1) (by norm_num)
    have hc : N13TwoChartLineTensor.secantV (0 : Q₂) 1 (-1) (-1) = 2 * X + 1 := by
      norm_num [N13TwoChartLineTensor.secantV]
      rw [show (Polynomial.C (2 : Q₂)) = 2 from rfl]
      ring
    rw [hc] at h
    simpa [C, B, cuspMumford, SexticMumford.mapCoeffs_u, SexticMumford.mapCoeffs_v,
      N13Mumford.cuspPoint, SexticMumford.pointMumford, SexticMumford.affinePointMumford]
      using h
  have hraw : SexticMumford.mumfordRaw Model basePair.mumford =
      (SexticMumford.mumfordRaw Model C * SexticMumford.mumfordRaw Model B) *
        (1, Multiplicative.ofAdd 1) := by
    apply Prod.ext
    · change SexticMumford.mumfordIdealUnit Model basePair.mumford.toSemi =
        (SexticMumford.mumfordIdealUnit Model C.toSemi *
          SexticMumford.mumfordIdealUnit Model B.toSemi) * 1
      rw [mul_one]
      apply Units.ext
      simp only [Units.val_mul, SexticMumford.coe_mumfordIdealUnit,
        ← FractionalIdeal.coeIdeal_mul]
      exact congrArg (fun I : Ideal R =>
        (I : N13IntegralFractionalHull.RationalFractionalIdeal)) hpair.symm
    · change Multiplicative.ofAdd (-1 : ℤ) =
        (Multiplicative.ofAdd (-1 : ℤ) * Multiplicative.ofAdd (-1 : ℤ)) *
          Multiplicative.ofAdd (1 : ℤ)
      decide
  change rawClass (SexticMumford.mumfordRaw Model basePair.mumford) = _
  rw [hraw, rawClass_mul, rawClass_mul]
  change SexticMumford.classOf Model (N13Infinity.positiveInfinityOrder Q₂) C +
    SexticMumford.classOf Model (N13Infinity.positiveInfinityOrder Q₂) B + infinityShift = _
  rw [cuspMumford_class, cuspMumford_class, baseTranslate, map_add]
end
end MazurProof.N13KernelBasePic
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedMappedSpecialFamily
noncomputable section
open N13KernelBaseDivisor N13KernelInfinityMultiplicity N13KernelGraphContraction
open N13KernelBasePic N13TwoChartPicardRealization N13EffectiveGraphData
open N13RationalKernelDoublingAdapter
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13RationalKernelDoublingAdapter.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
theorem representative_nonempty (z : Kernel) :
    Nonempty (MappedSpecialRepresentative
      (N13TwoAdicAbelChartSection.subgroupToPic Kernel z)) := by
  let D := N13CalibratedChooser.choose
    ((z : N13ConstructedSpecialization.G) + baseTranslate)
  obtain ⟨E, he, _, hn, hr, hs⟩ := HuangN13.N13KernelInfinityMultiplicity.chosen_translated_finite_graph z
  refine ⟨{ mumford := balancedGraph E he.1
            class_eq := ?_
            map_contract_eq_special := ?_ }⟩
  · rw [balancedGraph_class D E he.1 hn hr]
    rw [show D.toGenericPic = N13InfinityBaseChange.picMapRatToQ₂
      ((z : N13ConstructedSpecialization.G) + baseTranslate) from
        HuangN13.N13CalibratedChooser.choose_generic _]
    rw [map_add, basePic_eq_translated_twist]
    change N13InfinityBaseChange.picMapRatToQ₂ (z : N13ConstructedSpecialization.G) +
      N13InfinityBaseChange.picMapRatToQ₂ baseTranslate + infinityShift =
        N13InfinityBaseChange.picMapRatToQ₂ (z : N13ConstructedSpecialization.G) +
          (N13InfinityBaseChange.picMapRatToQ₂ baseTranslate + infinityShift)
    exact add_assoc _ _ _
  · exact balancedGraph_map_contract D E he.1 hr hs (chosen_translated_divisor z)
end
end MazurProof.N13ConstructedMappedSpecialFamily
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
theorem solution (z : MazurProof.N13KernelBaseDivisor.Kernel) :
    Nonempty (MazurProof.N13RationalKernelDoublingAdapter.MappedSpecialRepresentative
      (MazurProof.N13TwoAdicAbelChartSection.subgroupToPic MazurProof.N13KernelBaseDivisor.Kernel z)) := by
  exact MazurProof.N13ConstructedMappedSpecialFamily.representative_nonempty z
