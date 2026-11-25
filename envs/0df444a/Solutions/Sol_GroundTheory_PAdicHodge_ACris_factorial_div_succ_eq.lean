-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.factorial_div_succ_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:28:34.139834+00:00
-- url     : https://prove2.me/submissions/652207e3-e6c0-4240-99a5-bd1b90f66d6a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector Polynomial
open GroundTheory.PAdicHodge.ACris
variable (q : ℕ)
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution {n j : ℕ} (h : n ≤ j) :
    (j + 1).factorial / (n + 1) = n.factorial * ((j + 1).factorial / (n + 1).factorial) := by
  obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial (Nat.succ_le_succ h)
  rw [hc, Nat.factorial_succ, mul_assoc, Nat.mul_div_cancel_left _ n.succ_pos,
    ← mul_assoc, Nat.mul_div_cancel_left _ (Nat.mul_pos n.succ_pos n.factorial_pos)]
end GroundTheory.PAdicHodge.ACris
