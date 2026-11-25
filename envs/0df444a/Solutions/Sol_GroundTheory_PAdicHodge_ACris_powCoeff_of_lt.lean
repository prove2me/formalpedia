-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.powCoeff_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:18:10.991081+00:00
-- url     : https://prove2.me/submissions/29d7e6f1-9c41-4e04-814b-6df5b9634716

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
import Theorems.Thm_GroundTheory_PAdicHodge_coeff_one_add_X_pow_sub_one_pow_of_lt


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
theorem _root_.solution {N m : ℕ} (h : m < N) : powCoeff q N m = 0 :=
  coeff_one_add_X_pow_sub_one_pow_of_lt q h
end GroundTheory.PAdicHodge.ACris
