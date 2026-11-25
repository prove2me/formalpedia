-- Prove2me | solution 1 for GlobalTheory.T.mem_monicSquarefreeUnitConstPolys_iff_monic_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:12:08.037309+00:00
-- url     : https://prove2.me/submissions/ce02f3ea-6ef7-41e0-91a4-0cd29629dd64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemMonicSquarefreeUnitConstPolysIffMonicSquarefr
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemMonicSquarefreeUnitConstPolysIffMonicSquarefrStatement
import Theorems.Thm_GlobalTheory_BadShare_mem_sqSet_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ) (f : (ZMod g)[X]), f ∈ sqSet g N ↔ f.Monic ∧ f.natDegree = N ∧ Squarefree f ∧ f.coeff 0 ≠ 0 := by
  first | exact @GlobalTheory.BadShare.mem_sqSet_iff | exact GlobalTheory.BadShare.mem_sqSet_iff | (intros; apply GlobalTheory.BadShare.mem_sqSet_iff <;> assumption)
end _root_.GlobalTheory.T
