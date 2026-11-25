-- Prove2me | solution 1 for GroundTheory.LocalField.ratCircleChar_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:47:03.628435+00:00
-- url     : https://prove2.me/submissions/4cb27c6a-08d9-428f-9e3b-31a45ed98793

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalFourierExistence
import Theorems.Thm_GroundTheory_LocalField_ratAddCircleToReal_injective

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
theorem _root_.solution : Function.Injective ratCircleChar :=
  (AddCircle.injective_toCircle one_ne_zero).comp ratAddCircleToReal_injective
end GroundTheory.LocalField
