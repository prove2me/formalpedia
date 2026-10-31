-- Prove2me | solution 1 for HuangN13.N13ConstructedSpecialization.chosen_code_balance
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:15:11.411476+00:00
-- url     : https://prove2.me/submissions/27b70b82-186d-4067-8e61-0ed118bde6b8

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
namespace MazurProof.N13.TwoChartTensorCompatibility
noncomputable section
open N13TwoChartPicardRealization
/-- Tensoring two degree-two realizations gives the chart ideals of their
literal degree-four sum. It does not produce another `Data`. -/
theorem restrict_tensor_data (D E : Data) :
    N13TwoChartSpecialRestriction.restrict
        (N13TwoChartLineTensor.tensor D.charts E.charts) =
      N13SpecialDivisorCharts.tensor
        (N13SpecialDivisorCharts.ofDivisor D.specialDivisor)
        (N13SpecialDivisorCharts.ofDivisor E.specialDivisor) := by
  rw [restrict_tensor, restrict_data, restrict_data]
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
namespace MazurProof.N13CoherentChooserSpecification
noncomputable section
/-- The separate geometric tensor-normalization obligation. A proof must
produce four actual regular functions for every P,Q, with nonzero reductions,
matching principal ideal equations and one common overlap fraction.
This is a target to prove, not an assumed substitute for the end theorem. -/
def HasIntegralTensorComparisons (c : Chooser) : Prop :=
  ∀ P Q : G, Nonempty (N13CoherentChartComparison.IntegralComparison
    (N13TwoChartLineTensor.tensor (c.choose P).charts (c.choose Q).charts)
    (N13TwoChartLineTensor.tensor (c.choose (P + Q)).charts (c.choose 0).charts))
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
namespace MazurProof.N13CalibratedChooser
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking N13TwoChartPicardRealization N13PointDataCertificates
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem chooser_tensor_comparisons : N13CoherentChooserSpecification.HasIntegralTensorComparisons chooser := by
  intro P Q
  apply tensor_comparison_of_class_sum_eq _ _ _ _
    (HuangN13.N13CalibratedChooser.choose_certified P) (HuangN13.N13CalibratedChooser.choose_certified Q) (HuangN13.N13CalibratedChooser.choose_certified (P + Q)) (HuangN13.N13CalibratedChooser.choose_certified 0)
  simp only [HuangN13.N13CalibratedChooser.choose_generic, map_add, map_zero, add_zero]
end
end MazurProof.N13CalibratedChooser
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
theorem chosen_code_balance (P Q : G) :
    divisorCode (chosenDivisor P) + divisorCode (chosenDivisor Q) =
      divisorCode (chosenDivisor (P + Q)) + divisorCode (chosenDivisor 0) := by
  obtain ⟨h⟩ := N13CalibratedChooser.chooser_tensor_comparisons P Q
  have hred := h.reduce
  rw [N13.TwoChartTensorCompatibility.restrict_tensor_data,
    N13.TwoChartTensorCompatibility.restrict_tensor_data] at hred
  exact HuangN13.N13SpecialDegreeFourCode.degreeFourCode_eq_of_comparison_icf _ _ _ _ hred
end
end MazurProof.N13ConstructedSpecialization
end
end


set_option autoImplicit false
open Polynomial
theorem solution (P Q : MazurProof.N13ConstructedSpecialization.G) :
    MazurProof.N13SpecialAbelCode.divisorCode (MazurProof.N13ConstructedSpecialization.chosenDivisor P) + MazurProof.N13SpecialAbelCode.divisorCode (MazurProof.N13ConstructedSpecialization.chosenDivisor Q) =
      MazurProof.N13SpecialAbelCode.divisorCode (MazurProof.N13ConstructedSpecialization.chosenDivisor (P + Q)) + MazurProof.N13SpecialAbelCode.divisorCode (MazurProof.N13ConstructedSpecialization.chosenDivisor 0) := by
  exact MazurProof.N13ConstructedSpecialization.chosen_code_balance P Q
