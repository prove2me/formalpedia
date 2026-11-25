-- Prove2me | solution 1 for GroundTheory.LocalField.normedField_properSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:14:18.900161+00:00
-- url     : https://prove2.me/submissions/5fa902ce-43c8-4331-8f6e-5418224c7d80

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension

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
open ValuativeRel
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution :
    letI := normedField K
    ProperSpace K := by
  let := normedField K
  exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
end GroundTheory.LocalField
