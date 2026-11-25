-- Prove2me | solution 1 for GroundTheory.PAdicHodge.one_add_X_mul_mk_neg_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:19:08.584195+00:00
-- url     : https://prove2.me/submissions/bf1bd5d4-7007-4caa-8452-f38ac1569297

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries

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
open PowerSeries
namespace GroundTheory.PAdicHodge
theorem _root_.solution :
    (1 + X : ℚ⟦X⟧) * mk (fun n => algebraMap ℚ ℚ ((-1 : ℚ) ^ n)) = 1 := by
  ext n
  rw [add_mul, one_mul, map_add]
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_mk, coeff_mk, coeff_one, if_neg n.succ_ne_zero]
    simp [pow_succ]
end GroundTheory.PAdicHodge
