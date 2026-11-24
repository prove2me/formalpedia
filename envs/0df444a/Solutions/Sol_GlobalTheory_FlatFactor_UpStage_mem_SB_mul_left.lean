-- Prove2me | solution 1 for GlobalTheory.FlatFactor.UpStage.mem_SB_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:18:35.346971+00:00
-- url     : https://prove2.me/submissions/c8f9eadc-088a-4890-89b1-ba8510c765e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegrated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillingPartialEvalIntegralKernelTransla
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelIntegratesFreeEntries
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.FlatFactor GlobalTheory.FlatFactor.UpStage
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
omit [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.FlatFactor.UpStage
theorem _root_.solution (g : GL m k) (Θ : SB (Matrix m m' k)) :
    (fun t => Θ.1 (g.val * t)) ∈ SB (Matrix m m' k) := by
  have hc : Continuous fun t : Matrix m m' k => g.val * t := continuous_const.matrix_mul continuous_id
  have hc' : Continuous fun t : Matrix m m' k => (g⁻¹).val * t := continuous_const.matrix_mul continuous_id
  let h : Matrix m m' k ≃ₜ Matrix m m' k :=
    { toFun := fun t => g.val * t
      invFun := fun t => (g⁻¹).val * t
      left_inv := fun t => by simp [← Matrix.mul_assoc]
      right_inv := fun t => by simp [← Matrix.mul_assoc]
      continuous_toFun := hc
      continuous_invFun := hc' }
  have hΘ : IsLocallyConstant Θ.1 ∧ HasCompactSupport Θ.1 := Θ.2
  exact ⟨hΘ.1.comp_continuous hc, hΘ.2.comp_homeomorph h⟩
end GlobalTheory.FlatFactor.UpStage
