-- Prove2me | solution 1 for GlobalTheory.StepData.TypeDatum.hasTypes_Phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:24:34.392537+00:00
-- url     : https://prove2.me/submissions/9c74d521-f535-437e-af6a-c8370d24577d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_step_lam
import Theorems.Thm_GlobalTheory_StepData_om_of_mem_KO
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_Phi_mul_right
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_Phi_mul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open GlobalTheory.StepData.TypeDatum
variable (P : TypeDatum k a) {μ : kˣ →* ℂˣ}
namespace GlobalTheory.StepData.TypeDatum
theorem _root_.solution (hμ : IsTame μ) : HasTypes μ P.toLevel (P.step t μ hμ).toLevel (P.Phi t μ) := by
  refine ⟨fun g => funext fun x => ?_, fun h => funext fun x => ?_⟩
  · rw [om_of_mem_KO μ (P.le_KO g.2) (one_mem _), inv_one, Units.val_one, Matrix.one_mul, Phi_mul_right, rho_apply]
    simp; field_simp
  · rw [om_of_mem_KO μ (one_mem _) h.2.1, Units.val_one, Matrix.mul_one, ← map_inv (P.step t μ hμ).lam]
    erw [P.step_lam μ hμ h⁻¹ _ (P.corner_val _), ← rho_apply, P.Phi_mul_left hμ h⁻¹ x]
    rw [show ((h⁻¹ : P.stepJ t) : GL (a ⊕ t) k) = (h : GL (a ⊕ t) k)⁻¹ from rfl]
    simp; ring
end GlobalTheory.StepData.TypeDatum
