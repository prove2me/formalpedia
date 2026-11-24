-- Prove2me | solution 1 for GlobalTheory.SymChain.IterPattern.free_lr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:41:31.271885+00:00
-- url     : https://prove2.me/submissions/1eef1caf-6519-4ba9-a815-ca3ecf8cefe5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPatternStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.IterPattern
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ρ κ l j : ℕ} {t : Type}
namespace GlobalTheory.SymChain.IterPattern
theorem _root_.solution (x : Ix (Fin κ ⊕ Fin l) t j) (s : t) :
    FreeIx ρ (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inr s)) := by
  rcases x with a | ⟨i, s'⟩ <;> simp [ixSucc, FreeIx, (Fin.castSucc_lt_last _).le]
end GlobalTheory.SymChain.IterPattern
