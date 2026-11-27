-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.pred_mem_and_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:05.318968+00:00
-- url     : https://prove2.me/submissions/69b0f3cc-d3ca-4839-b753-57c9010dbd6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw
open GlobalTheory.Tw.PFlag
variable {n : ℕ} {k : Type} [Field k] {F : PFlag n k}
namespace GlobalTheory.Tw.PFlag
theorem _root_.solution {V : Submodule k (Fin n → k)} (hV : V ≠ ⊥) : F.pred V ∈ F.carrier ∧ F.pred V < V := by
  obtain ⟨M, hM, hmax⟩ := (wellFounded_gt (α := Submodule k (Fin n → k))).has_min {V' | V' ∈ F.carrier ∧ V' < V}
    ⟨⊥, F.bot_mem, bot_lt_iff_ne_bot.2 hV⟩
  have : F.pred V = M := le_antisymm (sSup_le fun V' h => by
    rcases F.chain.total h.1 hM.1 with h' | h'
    · exact h'
    · exact (eq_of_le_of_not_lt h' (hmax V' h)).ge) (le_sSup hM)
  rw [this]; exact hM
end GlobalTheory.Tw.PFlag
