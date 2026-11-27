-- Prove2me | solution 1 for GroundTheory.LocalField.ratCircleChar_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:49:38.901855+00:00
-- url     : https://prove2.me/submissions/7f76bb9c-583e-4f74-873b-8ca1c6a6ea44

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalFourierExistence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Topology Filter
open scoped WithZero Pointwise
namespace GroundTheory.LocalField
theorem _root_.solution (x : AddCircle (1 : ℚ)) :
    ratCircleChar x = AddCircle.toCircle (ratAddCircleToReal x) := rfl
end GroundTheory.LocalField
