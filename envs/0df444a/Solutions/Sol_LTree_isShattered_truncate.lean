-- Prove2me | solution 1 for LTree.isShattered_truncate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:36:27.380125+00:00
-- url     : https://prove2.me/submissions/08af6ae7-3313-43b2-81e2-3c36721bb44e

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Online
public import Theorems.Thm_LTree_nonempty_of_isShattered


set_option autoImplicit true
@[expose] public section
public section
namespace LTree
theorem _root_.solution {X : Type} {C : ConceptClass X Bool}
    {m : ℕ} (T : LTree X m) (hT : T.isShattered C) {n : ℕ} (h : n ≤ m) :
    (T.truncate h).isShattered C := by
  induction n generalizing m C with
  | zero => exact T.nonempty_of_isShattered hT
  | succ k ih =>
    match m, T, h, hT with
    | _ + 1, .branch x l r, h, hT =>
      simp only [LTree.isShattered] at hT
      obtain ⟨hwt, hwf, hsl, hsr⟩ := hT
      simp only [LTree.truncate]
      exact ⟨hwt, hwf, ih l hsl (Nat.le_of_succ_le_succ h),
             ih r hsr (Nat.le_of_succ_le_succ h)⟩
end LTree
