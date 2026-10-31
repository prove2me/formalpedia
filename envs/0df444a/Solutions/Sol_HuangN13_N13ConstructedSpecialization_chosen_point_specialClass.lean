-- Prove2me | solution 1 for HuangN13.N13ConstructedSpecialization.chosen_point_specialClass
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:15:08.669061+00:00
-- url     : https://prove2.me/submissions/29e7f53f-4186-417f-b5bf-b68d3cbf44a6

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SeparationDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore
import Theorems.Thm_HuangN13_N13CalibratedChooser_choose_certified
import Theorems.Thm_HuangN13_N13CalibratedChooser_choose_generic
import Theorems.Thm_HuangN13_N13MarkedTensorComparison_exists_integral_tensor_comparison
import Theorems.Thm_HuangN13_N13PointDataCertificates_rationalPoint_certified
import Theorems.Thm_HuangN13_N13SpecialDegreeFourCode_degreeFourCode_eq_of_comparison_icf
import Theorems.Thm_MazurProof_N13EffectiveDataCompatibility_cancel_invertible_ideal
import Theorems.Thm_MazurProof_N13GoodModelTwo_affineEquation_iff_fixed

set_option autoImplicit false

namespace MazurProof.N13SpecialDegreeFourCode
end MazurProof.N13SpecialDegreeFourCode
section
section
set_option autoImplicit false
namespace MazurProof.N13.TwoChartTensorCompatibility
noncomputable section
open N13TwoChartPicardRealization
/-- A realization determines the complete reduced pair of chart ideals. -/
theorem restrict_data (D : Data) :
    N13TwoChartSpecialRestriction.restrict D.charts =
      N13SpecialDivisorCharts.ofDivisor D.specialDivisor := by
  exact N13TwoChartSpecialRestriction.ChartPair.ext
    D.special_affine D.special_infinity
end
end MazurProof.N13.TwoChartTensorCompatibility
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
namespace MazurProof.N13CoherentChartComparison
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The reduction of an actual whole-chart principal comparison is again
such a comparison. Obtaining this input for normalized representatives is a
separate geometric theorem. -/
def IntegralComparison.reduce {L M : Line} (h : IntegralComparison L M) :
    SpecialComparison (N13TwoChartSpecialRestriction.restrict L)
      (N13TwoChartSpecialRestriction.restrict M) where
  aNum := N13GeneralizedMumfordReduction.reduceCoordinate h.aNum
  aDen := N13GeneralizedMumfordReduction.reduceCoordinate h.aDen
  iNum := N13IntegralInfinityReduction.reduceCoordinate h.iNum
  iDen := N13IntegralInfinityReduction.reduceCoordinate h.iDen
  aNum_ne := h.aNum_ne
  aDen_ne := h.aDen_ne
  iNum_ne := h.iNum_ne
  iDen_ne := h.iDen_ne
  affine_eq := map_cleared_ideal_eq _ _ _ _ _ h.affine_eq
  infinity_eq := map_cleared_ideal_eq _ _ _ _ _ h.infinity_eq
  overlap_eq := by
    have hm := congrArg N13OverlapReductionCompatibility.reduceInfinityOverlap h.overlap_eq
    have ha (a : A) :
        N13OverlapReductionCompatibility.reduceInfinityOverlap
            (N13OrdinaryCurveOverlap.affineToInfinityOverlap a) =
          N13SpecialCurveOverlap.affineToInfinityOverlap
            (N13GeneralizedMumfordReduction.reduceCoordinate a) :=
      DFunLike.congr_fun
        N13TwoChartSpecialRestriction.reduceInfinityOverlap_comp_affineToInfinityOverlap a
    have hi (i : B) :
        N13OverlapReductionCompatibility.reduceInfinityOverlap (algebraMap B O i) =
          algebraMap Bs Os (N13IntegralInfinityReduction.reduceCoordinate i) :=
      DFunLike.congr_fun
        N13OverlapReductionCompatibility.reduceInfinityOverlap_comp_algebraMap i
    simpa only [map_mul, ha, hi] using hm
end
end MazurProof.N13CoherentChartComparison
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
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13EffectiveDataCompatibility.instIsFractionRingAF
def cancel_tensor_right (L M U : Line)
    (h : N13CoherentChartComparison.IntegralComparison (tensor L U) (tensor M U)) :
    N13CoherentChartComparison.IntegralComparison L M where
  aNum := h.aNum
  aDen := h.aDen
  iNum := h.iNum
  iDen := h.iDen
  aNum_ne := h.aNum_ne
  aDen_ne := h.aDen_ne
  iNum_ne := h.iNum_ne
  iDen_ne := h.iDen_ne
  affine_eq := MazurProof.N13EffectiveDataCompatibility.cancel_invertible_ideal (K := F) _ _ U.affineIdeal U.affine_isUnit
    (by simpa only [N13TwoChartLineTensor.tensor_affineIdeal, mul_assoc] using h.affine_eq)
  infinity_eq := MazurProof.N13EffectiveDataCompatibility.cancel_invertible_ideal (K := N13IntegralInfinityPointSpread.FunctionField)
    _ _ U.infinityIdeal U.infinity_isUnit
    (by simpa only [N13TwoChartLineTensor.tensor_infinityIdeal, mul_assoc] using h.infinity_eq)
  overlap_eq := h.overlap_eq
end
end MazurProof.N13EffectiveDataCompatibility
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
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem tensor_comparison_of_class_sum_eq
    (D₀ D₁ D₂ D₃ : Data)
    (h₀ : Certified D₀) (h₁ : Certified D₁) (h₂ : Certified D₂) (h₃ : Certified D₃)
    (hclass : D₀.toGenericPic + D₁.toGenericPic = D₂.toGenericPic + D₃.toGenericPic) :
    Nonempty (N13CoherentChartComparison.IntegralComparison
      (tensor D₀.charts D₁.charts) (tensor D₂.charts D₃.charts)) := by
  obtain ⟨E₀, hc₀, hr₀, hs₀, hm₀⟩ := h₀
  obtain ⟨E₁, hc₁, hr₁, hs₁, hm₁⟩ := h₁
  obtain ⟨E₂, hc₂, hr₂, hs₂, hm₂⟩ := h₂
  obtain ⟨E₃, hc₃, hr₃, hs₃, hm₃⟩ := h₃
  exact HuangN13.N13MarkedTensorComparison.exists_integral_tensor_comparison E₀ E₁ E₂ E₃ hc₀ hc₁ hc₂ hc₃
    D₀ D₁ D₂ D₃ hr₀ hr₁ hr₂ hr₃ hs₀ hs₁ hs₂ hs₃ hm₀ hm₁ hm₂ hm₃ hclass
end
end MazurProof.N13EffectiveDataCompatibility
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
theorem comparison_of_generic_eq (D E : Data) (hD : Certified D) (hE : Certified E)
    (heq : D.toGenericPic = E.toGenericPic) :
    Nonempty (N13CoherentChartComparison.IntegralComparison D.charts E.charts) := by
  obtain ⟨h⟩ := tensor_comparison_of_class_sum_eq D D E D hD hD hE hD
    (by rw [heq])
  exact ⟨cancel_tensor_right D.charts E.charts D.charts h⟩
end
end MazurProof.N13EffectiveDataCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CoherentChooserSpecification
noncomputable section
abbrev Data := N13TwoChartPicardRealization.Data
end
end MazurProof.N13CoherentChooserSpecification
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CoherentChooserSpecification
noncomputable section
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- Pointwise realization and geometric compatibility with rational points.
No additive law for the special code occurs in this specification. -/
structure Chooser where
  choose : G → Data
  generic_eq : ∀ P, (choose P).toGenericPic = N13InfinityBaseChange.picMapRatToQ₂ P
  saturated : ∀ P, N13TwoChartPicardRealization.AffineVerticallySaturated (choose P).charts
  point_compatible : ∀ P : N13RationalPointEndgame.RationalCurvePoint,
    Nonempty (N13CoherentChartComparison.IntegralComparison
      (choose (N13RationalPointEndgame.rationalAbel P)).charts
      (N13RationalCurvePointPicardRealization.data P).realization.charts)
end
end MazurProof.N13CoherentChooserSpecification
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
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
def chooser : N13CoherentChooserSpecification.Chooser where
  choose := choose
  generic_eq := HuangN13.N13CalibratedChooser.choose_generic
  saturated P := by
    obtain ⟨E, _, _, hs, _⟩ := HuangN13.N13CalibratedChooser.choose_certified P
    exact hs
  point_compatible P := by
    apply comparison_of_generic_eq _ _ (HuangN13.N13CalibratedChooser.choose_certified _) (HuangN13.N13PointDataCertificates.rationalPoint_certified P)
    rw [HuangN13.N13CalibratedChooser.choose_generic, (N13RationalCurvePointPicardRealization.data P).generic_eq]
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
/-- First lemma: every member of the canonical hyperelliptic pencil has
code zero. The two sheets have opposite point codes. -/
@[simp] theorem divisorCode_canonicalDivisor
    (B : BasePoint) :
    divisorCode (canonicalDivisor B) = 0 := by
  simp [divisorCode, pointCode, N13AbelFiberTwoModel.curvePointEquiv, canonicalDivisor]
  cases B <;> simp [baseAmplitude]
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
/-- Second lemma: the explicit code is constant on every AbelRel class. -/
theorem divisorCode_eq_of_abelRel
    {D E : EffectiveDivisorTwo}
    (h : AbelRel D E) :
    divisorCode D = divisorCode E := by
  -- The AbelRel is D = E or both are canonical
  rcases h with rfl | ⟨hD, hE⟩
  · rfl
  · -- Both D and E are canonical divisors, so both have code 0
    have hD0 : divisorCode D = 0 := by
      obtain ⟨bD, rfl⟩ := hD
      exact divisorCode_canonicalDivisor bD
    have hE0 : divisorCode E = 0 := by
      obtain ⟨bE, rfl⟩ := hE
      exact divisorCode_canonicalDivisor bE
    rw [hD0, hE0]
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
/-- Point code read in the explicit `(base point, sheet)` coordinates. -/
def codeBP (p : BasePoint × K) : Code :=
  if p.2 = 0 then baseAmplitude p.1 else -(baseAmplitude p.1)
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
/-- Divisor code read in the explicit coordinates. -/
def dcodeBP : Sym2 (BasePoint × K) → Code :=
  Sym2.lift ⟨fun p q => codeBP p + codeBP q, fun p q => by simp [add_comm]⟩
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
theorem divisorCode_eq_dcodeBP (D : EffectiveDivisorTwo) :
    divisorCode D = dcodeBP (D.map curvePointEquiv) := by
  induction D using Sym2.ind with
  | h P Q => rfl
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
theorem map_curvePointEquiv_injective :
    Function.Injective (fun D : EffectiveDivisorTwo => D.map curvePointEquiv) :=
  Sym2.map.injective curvePointEquiv.injective
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
theorem isCanonical_iff_canonBP (D : EffectiveDivisorTwo) :
    IsCanonical D ↔ CanonBP (D.map curvePointEquiv) := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, map_canonicalDivisor b⟩
  · rintro ⟨b, hb⟩
    refine ⟨b, map_curvePointEquiv_injective ?_⟩
    simp only
    rw [map_canonicalDivisor, hb]
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
/-- The finite separation fact behind A04 (checked by `decide`). -/
theorem dcodeBP_separates :
    ∀ S T : Sym2 (BasePoint × K),
      dcodeBP S = dcodeBP T → S = T ∨ (CanonBP S ∧ CanonBP T) := by
  decide
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
/-- A04: the code is a complete invariant of `AbelRel`. -/
theorem divisorCode_eq_iff_abelRel (D E : EffectiveDivisorTwo) :
    divisorCode D = divisorCode E ↔ AbelRel D E := by
  constructor
  · intro h
    rw [divisorCode_eq_dcodeBP, divisorCode_eq_dcodeBP] at h
    rcases dcodeBP_separates _ _ h with h | ⟨hD, hE⟩
    · exact Or.inl (map_curvePointEquiv_injective h)
    · exact Or.inr ⟨(isCanonical_iff_canonBP D).2 hD, (isCanonical_iff_canonBP E).2 hE⟩
  · exact divisorCode_eq_of_abelRel
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
/-- A05: the code on the special Abel quotient. -/
def picCode : PicTwoSetModel → Code :=
  Quotient.lift divisorCode (fun _ _ h => divisorCode_eq_of_abelRel h)
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
/-- A06 (injectivity). -/
theorem picCode_injective : Function.Injective picCode := by
  intro x y
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  intro h
  exact (abel_eq_iff _ _).2 ((divisorCode_eq_iff_abelRel _ _).1 h)
end
end MazurProof.N13SpecialAbelCode
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
def tensor_comparison_right
    (L M U : N13TwoChartSpecialRestriction.ChartPair) (h : SpecialComparison L M) :
    SpecialComparison (tensor L U) (tensor M U) where
  aNum := h.aNum
  aDen := h.aDen
  iNum := h.iNum
  iDen := h.iDen
  aNum_ne := h.aNum_ne
  aDen_ne := h.aDen_ne
  iNum_ne := h.iNum_ne
  iDen_ne := h.iDen_ne
  affine_eq := by
    change Ideal.span ({h.aNum} : Set As) * (L.affineIdeal * U.affineIdeal) =
      Ideal.span ({h.aDen} : Set As) * (M.affineIdeal * U.affineIdeal)
    rw [← mul_assoc, h.affine_eq, mul_assoc]
  infinity_eq := by
    change Ideal.span ({h.iNum} : Set Bs) * (L.infinityIdeal * U.infinityIdeal) =
      Ideal.span ({h.iDen} : Set Bs) * (M.infinityIdeal * U.infinityIdeal)
    rw [← mul_assoc, h.infinity_eq, mul_assoc]
  overlap_eq := h.overlap_eq
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
theorem divisorCode_eq_of_comparison (D E : EffectiveDivisorTwo)
    (h : SpecialComparison (ofDivisor D) (ofDivisor E)) : divisorCode D = divisorCode E := by
  have he := HuangN13.N13SpecialDegreeFourCode.degreeFourCode_eq_of_comparison_icf D D E D
    (tensor_comparison_right _ _ (ofDivisor D) h)
  exact add_right_cancel he
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
theorem chosen_point_specialClass (P : N13RationalPointEndgame.RationalCurvePoint) :
    (N13CalibratedChooser.choose (N13RationalPointEndgame.rationalAbel P)).toSpecialPic =
      N13RationalPointEndgame.specialPointClass (N13ProperCurveReduction.reduceCurve P) := by
  obtain ⟨h⟩ := N13CalibratedChooser.chooser.point_compatible P
  have hred := h.reduce
  rw [N13.TwoChartTensorCompatibility.restrict_data,
    N13.TwoChartTensorCompatibility.restrict_data] at hred
  have he := divisorCode_eq_of_comparison _ _ hred
  have hs : (N13CalibratedChooser.choose (N13RationalPointEndgame.rationalAbel P)).toSpecialPic =
      (N13RationalCurvePointPicardRealization.data P).realization.toSpecialPic := by
    apply picCode_injective
    exact he
  exact hs.trans (N13RationalCurvePointPicardRealization.data P).special_eq
end
end MazurProof.N13ConstructedSpecialization
end
end


set_option autoImplicit false
open Polynomial
theorem solution (P : MazurProof.N13RationalPointEndgame.RationalCurvePoint) :
    (MazurProof.N13CalibratedChooser.choose (MazurProof.N13RationalPointEndgame.rationalAbel P)).toSpecialPic =
      MazurProof.N13RationalPointEndgame.specialPointClass (MazurProof.N13ProperCurveReduction.reduceCurve P) := by
  exact MazurProof.N13ConstructedSpecialization.chosen_point_specialClass P
