-- Prove2me | solution 1 for GroundTheory.PAdicHodge.one_add_X_mul_geom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:50:12.176591+00:00
-- url     : https://prove2.me/submissions/686ec781-e432-4111-aaa8-6e9ccb582fda

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRSeries
import Theorems.Thm_GroundTheory_PAdicHodge_seriesEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.seriesEval_X

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open PowerSeries
namespace GroundTheory.PAdicHodge
theorem _root_.solution : (1 + X : ℚ⟦X⟧) * mk (fun n => algebraMap ℚ ℚ ((-1) ^ n)) = 1 := by
  ext n
  rw [add_mul, one_mul, map_add, coeff_one]
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_mk, coeff_mk, if_neg (Nat.succ_ne_zero n)]
    simp [pow_succ]
end GroundTheory.PAdicHodge
