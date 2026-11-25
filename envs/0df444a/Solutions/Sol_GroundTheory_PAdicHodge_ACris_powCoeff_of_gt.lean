-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.powCoeff_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:37:45.358849+00:00
-- url     : https://prove2.me/submissions/6cdfe7ea-47ff-4a9a-b519-a8616f1cabde

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_natDegree_one_add_X_pow_sub_one_pow_le

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
theorem _root_.solution {N m : ℕ} (h : q * N < m) : powCoeff q N m = 0 :=
  coeff_eq_zero_of_natDegree_lt ((natDegree_one_add_X_pow_sub_one_pow_le q N).trans_lt h)
end GroundTheory.PAdicHodge.ACris
