-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.mul_sub_one_add_one_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:13:42.729574+00:00
-- url     : https://prove2.me/submissions/aeb61553-cff2-4fae-88e6-97a420b34254

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaPeriod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {p : ℕ} [hp : Fact p.Prime]
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution (k : ℕ) : k * (p - 1) + 1 ≤ p ^ k := by
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.out.one_le).symm⟩
  rw [hm, Nat.add_sub_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h1 : 1 ≤ (m + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos m)
    nlinarith
end GroundTheory.PAdicHodge.ACris
