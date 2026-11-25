-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.factorization_succ_le_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:19:14.808805+00:00
-- url     : https://prove2.me/submissions/59405b8b-f281-4896-8f27-fa8725bb1789

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaPeriod
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_mul_sub_one_add_one_le_pow

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
theorem _root_.solution (n : ℕ) : (n + 1).factorization p ≤ n / (p - 1) := by
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  rw [Nat.le_div_iff_mul_le hp1]
  have h1 := Nat.ordProj_le p (Nat.succ_ne_zero n)
  have h2 := mul_sub_one_add_one_le_pow (p := p) ((n + 1).factorization p)
  generalize (n + 1).factorization p = k at h1 h2 ⊢
  generalize p ^ k = A at h1 h2
  generalize k * (p - 1) = B at h2 ⊢
  omega
end GroundTheory.PAdicHodge.ACris
