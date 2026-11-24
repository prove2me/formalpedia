-- Prove2me | solution 1 for GlobalTheory.AutQuotCheck.cls_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:13:26.561245+00:00
-- url     : https://prove2.me/submissions/5f742440-7321-4232-a084-6c7cd95d0249

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_RightInvariantOfCovolume
import Theorems.Thm_GlobalTheory_AutQuotCheck_cls_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.AutQuotCheck
variable {G : Type} [Group G] (Γ : Subgroup G)
open MeasureTheory
open scoped Pointwise
variable {G : Type} [Group G] (Γ : Subgroup G)
namespace GlobalTheory.AutQuotCheck
namespace _root_.GlobalTheory.AutQuotCheck
theorem _root_.solution (γ : Γ) (x : G) :
    _root_.GlobalTheory.AutQuotCheck.cls Γ (γ • x) = _root_.GlobalTheory.AutQuotCheck.cls Γ x := by
  rw [_root_.GlobalTheory.AutQuotCheck.cls_eq_iff]
  refine ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, ?_⟩
  rw [Subgroup.smul_def, smul_eq_mul, inv_mul_cancel_left]
end _root_.GlobalTheory.AutQuotCheck
end GlobalTheory.AutQuotCheck
