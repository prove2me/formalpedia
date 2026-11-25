-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.two_mul_mul_sub_one_le_pow_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:14:05.59988+00:00
-- url     : https://prove2.me/submissions/ef4cd945-65a5-477a-8117-cb2c696d5b2d

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
theorem _root_.solution (k : ℕ) : 2 * k * (p - 1) ≤ p ^ k + p := by
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.out.one_le).symm⟩
  have hm1 : 1 ≤ m := by have := hp.out.two_le; omega
  rw [hm, Nat.add_sub_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
    rcases k with _ | k
    · rw [zero_add, pow_one]; omega
    · have h2 : 2 ≤ (m + 1) ^ (k + 1) :=
        calc 2 ≤ (m + 1) ^ 1 := by rw [pow_one]; omega
          _ ≤ (m + 1) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      rw [pow_succ]
      nlinarith
end GroundTheory.PAdicHodge.ACris
