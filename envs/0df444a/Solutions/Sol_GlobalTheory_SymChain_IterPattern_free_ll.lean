-- Prove2me | solution 1 for GlobalTheory.SymChain.IterPattern.free_ll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:40:15.084729+00:00
-- url     : https://prove2.me/submissions/4ab94eff-9ecf-43ac-9375-9f6e4a459a4a

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
theorem _root_.solution (x y : Ix (Fin κ ⊕ Fin l) t j) :
    FreeIx ρ (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inl y)) ↔ FreeIx ρ x y := by
  rcases x with a | ⟨i, s⟩ <;> rcases y with b | ⟨i', s'⟩ <;> simp [ixSucc, FreeIx]
end GlobalTheory.SymChain.IterPattern
