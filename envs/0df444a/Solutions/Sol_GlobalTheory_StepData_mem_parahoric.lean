-- Prove2me | solution 1 for GlobalTheory.StepData.mem_parahoric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:56:01.684422+00:00
-- url     : https://prove2.me/submissions/c4513825-6d68-40b0-8f3a-88c51d571a32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_exists_diag_blocks


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
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
variable {r s s' : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
namespace GlobalTheory.StepData
theorem _root_.solution {δ : kˣ →* ℂˣ} {hδ : IsTame δ} {h : GL (r ⊕ s) k} :
    h ∈ (parahoric r s δ hδ).J ↔ h ∈ KO k (r ⊕ s) ∧ MaxM h.val.toBlocks₂₁ :=
  (TypeDatum.mem_stepJ_iff _).trans
    ⟨fun H => ⟨H.1, H.2.2⟩, fun H => ⟨H.1, (exists_diag_blocks H.1 H.2).1, H.2⟩⟩
end GlobalTheory.StepData
