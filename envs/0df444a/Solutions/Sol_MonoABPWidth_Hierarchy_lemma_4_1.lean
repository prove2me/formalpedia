-- Prove2me | solution 1 for MonoABPWidth.Hierarchy.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:25:50.752468+00:00
-- url     : https://prove2.me/submissions/8b4fd510-0737-42de-b4c1-479692b2e874

import Mathlib
import Definitions.Def_MonoABPWidth_Hierarchy_simplicity
import Definitions.Def_SetMultCost_imm
import Theorems.Thm_MonoABPWidth_Hierarchy_lemma_A_2
import Theorems.Thm_MonoABPWidth_Hierarchy_lemma_A_4

section
set_option autoImplicit false

namespace MonoABPWidth.Hierarchy

theorem chk_lemma_4_1 (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (A : MABP (SetMultCost.IMMVar k n)) (hzero : A.output ≠ 0)
    (hsub : A.output.support ⊆ (SetMultCost.imm ℝ k n).support) :
    ∃ B : MABP (SetMultCost.IMMVar k n),
      B.width ≤ A.width ∧ B.depth ≤ A.depth ∧ B.Simple ∧ B.output = A.output := by
  obtain ⟨B, hw, hd, hrel, hnp, hout⟩ := MonoABPWidth.Hierarchy.lemma_A_2 A hzero
  refine ⟨B, hw, hd, ⟨hrel, hnp, ?_⟩, hout⟩
  exact MonoABPWidth.Hierarchy.lemma_A_4 k n hk hn B hrel (hout ▸ hsub)

end MonoABPWidth.Hierarchy
end

theorem solution : type_of% @MonoABPWidth.Hierarchy.chk_lemma_4_1 := @MonoABPWidth.Hierarchy.chk_lemma_4_1
