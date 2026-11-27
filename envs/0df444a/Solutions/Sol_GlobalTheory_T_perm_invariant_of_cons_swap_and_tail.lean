-- Prove2me | solution 1 for GlobalTheory.T.perm_invariant_of_cons_swap_and_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:34:10.118544+00:00
-- url     : https://prove2.me/submissions/41e67cdf-f25d-47e7-97ea-03a0d876de56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PermInvariantOfConsSwapAndTail
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PermInvariantOfConsSwapAndTailStatement
import Theorems.Thm_GlobalTheory_perm_invariant_of_cons_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (α : Type 1) (n : ℕ) (F : (Fin (n + 2) → α) → ℝ), (∀ (a : α) (L : Fin (n + 1) → α) (e : Equiv.Perm (Fin (n + 1))), F (Fin.cons a fun i => L (e i)) = F (Fin.cons a L)) → (∀ (a b : α) (L : Fin n → α), F (Fin.cons a (Fin.cons b L : Fin (n + 1) → α)) = F (Fin.cons b (Fin.cons a L : Fin (n + 1) → α))) → ∀ (L : Fin (n + 2) → α) (e : Equiv.Perm (Fin (n + 2))), F (fun i => L (e i)) = F L := by
  first | exact @GlobalTheory.perm_invariant_of_cons_swap | exact GlobalTheory.perm_invariant_of_cons_swap | (intros; apply GlobalTheory.perm_invariant_of_cons_swap <;> assumption)
end _root_.GlobalTheory.T
