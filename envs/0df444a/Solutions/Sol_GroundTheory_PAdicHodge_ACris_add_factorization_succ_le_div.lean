-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.add_factorization_succ_le_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:19:12.091995+00:00
-- url     : https://prove2.me/submissions/f9bf1306-96d4-4800-999f-b88ce52fde08

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaPeriod
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_two_mul_mul_sub_one_le_pow_add

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
theorem _root_.solution {n j : ℕ} (hn : 2 * (p - 1) * j + 3 * p ≤ n) :
    j + (n + 1).factorization p ≤ n / (p - 1) := by
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  rw [Nat.le_div_iff_mul_le hp1]
  have h1 := Nat.ordProj_le p (Nat.succ_ne_zero n)
  have h2 := two_mul_mul_sub_one_le_pow_add (p := p) ((n + 1).factorization p)
  generalize (n + 1).factorization p = k at h1 h2 ⊢
  generalize p ^ k = A at h1 h2
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.out.one_le).symm⟩
  subst hm
  rw [Nat.add_sub_cancel] at hn h2 ⊢
  nlinarith
end GroundTheory.PAdicHodge.ACris
