-- Prove2me | solution 1 for GlobalTheory.StepData.hasTypes_parPhi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:27:07.286671+00:00
-- url     : https://prove2.me/submissions/a007821b-b739-48b7-88ac-a083e3795bf1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_step_lam
import Theorems.Thm_GlobalTheory_StepData_om_of_mem_KO
import Theorems.Thm_GlobalTheory_StepData_parPhi_mul_right
import Theorems.Thm_GlobalTheory_StepData_parPhi_mul_left
import Theorems.Thm_GlobalTheory_StepData_valuation_det_of_mem_KO


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
variable {r s s' : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s] [Fintype s'] [DecidableEq s']
  {δ : kˣ →* ℂˣ}
namespace GlobalTheory.StepData
theorem _root_.solution (hδ : IsTame δ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) :
    HasTypes (ν * δ) (parahoric r s' δ hδ).toLevel (parahoric r s δ hδ).toLevel (parPhi δ) := by
  refine ⟨fun g => funext fun x => ?_, fun h => funext fun x => ?_⟩
  · rw [om_of_mem_KO _ g.2.1 (one_mem _), inv_one, Units.val_one, Matrix.one_mul]
    erw [parPhi_mul_right hδ g x, (TypeDatum.full k r).step_lam δ hδ g _ (TypeDatum.corner_val _ _),
      ← TypeDatum.rho_apply]
    simp [hν _ (valuation_det_of_mem_KO g.2.1)]; ring
  · rw [om_of_mem_KO _ (one_mem _) h.2.1, Units.val_one, Matrix.mul_one, ← map_inv (parahoric r s δ hδ).lam]
    erw [(TypeDatum.full k r).step_lam δ hδ h⁻¹ _ (TypeDatum.corner_val _ _), ← TypeDatum.rho_apply,
      parPhi_mul_left hδ h⁻¹ x]
    rw [show ((h⁻¹ : (TypeDatum.full k r).stepJ s) : GL (r ⊕ s) k) = (h : GL (r ⊕ s) k)⁻¹ from rfl]
    simp [hν _ (valuation_det_of_mem_KO h.2.1)]; ring
end GlobalTheory.StepData
