-- Prove2me | solution 1 for GroundTheory.LocalField.principalFiltration_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:46:57.455523+00:00
-- url     : https://prove2.me/submissions/399dc698-b359-4fa4-844f-c52f124a5048

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicExp
import Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsModule
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution : Antitone (principalFiltration K) := by
  intro j k hjk u hu
  rw [mem_principalFiltration] at hu ⊢
  exact valBall_antitone (by omega) hu
end GroundTheory.LocalField
