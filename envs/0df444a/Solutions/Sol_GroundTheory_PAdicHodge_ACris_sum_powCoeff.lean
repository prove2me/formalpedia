-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.sum_powCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:17:27.513808+00:00
-- url     : https://prove2.me/submissions/95ef88de-d39c-4ce2-a180-2e684bb9a98f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
import Theorems.Thm_GroundTheory_PAdicHodge_log_pow_coeff_int


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
theorem _root_.solution (j : ℕ) :
    ∑ n ∈ Finset.range (j + 1), (-1 : ℤ) ^ n * powCoeff q (n + 1) (j + 1) *
      (((j + 1).factorial / (n + 1) : ℕ) : ℤ) = (-1) ^ j * q * j.factorial := by
  have h := log_pow_coeff_int q (j + 1) (Nat.succ_pos j)
  have hI : Finset.Icc 1 (j + 1) = Finset.Ico 1 (j + 2) := by ext; simp; omega
  rw [hI, Finset.sum_Ico_eq_sum_range] at h
  simp only [Nat.add_sub_cancel, show j + 2 - 1 = j + 1 by omega] at h
  rw [← h]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [add_comm 1 n, Nat.add_sub_cancel, powCoeff]
end GroundTheory.PAdicHodge.ACris
