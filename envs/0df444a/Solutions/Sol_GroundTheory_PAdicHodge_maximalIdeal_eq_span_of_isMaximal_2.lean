-- Prove2me | solution 2 for GroundTheory.PAdicHodge.maximalIdeal_eq_span_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:48:49.34165+00:00
-- url     : https://prove2.me/submissions/e0efa8c1-9670-47a6-a365-b00d00832eaa

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus

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
open Ideal WittVector IsLocalRing
variable {B : Type*} [CommRing B]
namespace GroundTheory.PAdicHodge
theorem _root_.solution [IsLocalRing B] {π : B} (hmax : (span {π}).IsMaximal) :
    maximalIdeal B = span {π} :=
  (IsLocalRing.eq_maximalIdeal hmax).symm
end GroundTheory.PAdicHodge
