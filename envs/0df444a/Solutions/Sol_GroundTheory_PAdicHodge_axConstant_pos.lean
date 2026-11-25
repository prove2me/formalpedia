-- Prove2me | solution 1 for GroundTheory.PAdicHodge.axConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:29:30.345802+00:00
-- url     : https://prove2.me/submissions/c0bb0cc6-5b19-42fe-8a3a-2f670708ecde

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Theorems.Thm_GroundTheory_PAdicHodge_one_le_axConstant

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
open Polynomial
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution : 0 < axConstant p := one_le_axConstant.trans_lt' one_pos
end GroundTheory.PAdicHodge
