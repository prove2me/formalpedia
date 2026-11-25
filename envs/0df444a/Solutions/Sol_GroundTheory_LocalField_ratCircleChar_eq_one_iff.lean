-- Prove2me | solution 1 for GroundTheory.LocalField.ratCircleChar_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:55:35.6965+00:00
-- url     : https://prove2.me/submissions/825dbc6a-55c6-467c-858c-1570fca11aa0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalFourierExistence
import Theorems.Thm_GroundTheory_LocalField_ratCircleChar_injective

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
theorem _root_.solution {x : AddCircle (1 : ℚ)} : ratCircleChar x = 1 ↔ x = 0 := by
  constructor
  · intro h
    apply ratCircleChar_injective
    rw [h, AddChar.map_zero_eq_one]
  · rintro rfl
    exact AddChar.map_zero_eq_one _
end GroundTheory.LocalField
