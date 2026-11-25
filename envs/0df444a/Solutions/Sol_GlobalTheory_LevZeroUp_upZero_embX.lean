-- Prove2me | solution 1 for GlobalTheory.LevZeroUp.upZero_embX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:59:27.565797+00:00
-- url     : https://prove2.me/submissions/bbb63e0b-fa63-46e7-9613-f6dda5aecbe2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UpZeroMemLev
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LevelZeroUniformizerFrameUnipotentAndEmbedGL
import Theorems.Thm_GlobalTheory_LevZeroUp_back_eps
import Theorems.Thm_GlobalTheory_LevZeroUp_levelZeroOldIndexOfNew_inr
import Theorems.Thm_GlobalTheory_LevZeroUp_upZero_entry
import Theorems.Thm_GlobalTheory_LevZeroUp_xZero_symm
import Theorems.Thm_GlobalTheory_StepData_reGL_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.LevZeroUp
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LevZeroGen GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
namespace GlobalTheory.LevZeroUp
theorem _root_.solution (γ : GL (Fin κ) k) :
    upZero S t (embX (s + 1) γ) = embX (s + 1) (reGL (xZero (Fin κ) t) γ) := by
  ext r c
  rw [upZero_entry]
  rcases r with ((r | r) | ⟨r, _⟩) | r
  · rcases c with ((c | c) | ⟨c, _⟩) | c
    · rw [back_eps, back_eps]
      simp [embX, scal, reGL_val, xZero_symm]
    · exact c.elim0
    · exact c.elim0
    · rw [back_eps, levelZeroOldIndexOfNew_inr]
      simp [embX]
  · exact r.elim0
  · exact r.elim0
  · rcases c with ((c | c) | ⟨c, _⟩) | c
    · rw [levelZeroOldIndexOfNew_inr, back_eps]
      simp [embX]
    · exact c.elim0
    · exact c.elim0
    · rw [levelZeroOldIndexOfNew_inr, levelZeroOldIndexOfNew_inr]
      by_cases e : r = c
      · subst e; simp [embX, scal, Matrix.one_apply]
      · simp [embX, Matrix.one_apply, e]
end GlobalTheory.LevZeroUp
