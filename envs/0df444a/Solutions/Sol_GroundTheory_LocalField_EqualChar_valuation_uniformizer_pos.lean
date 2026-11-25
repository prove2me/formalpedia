-- Prove2me | solution 1 for GroundTheory.LocalField.EqualChar.valuation_uniformizer_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:38:48.584564+00:00
-- url     : https://prove2.me/submissions/46ac519b-ebbf-4a75-bf85-e537ec9f5705

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesTeichmuller
import Definitions.Def_GroundTheory_LocalFields_ExamplesLaurent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsLocalRing Topology Filter WithZero HahnSeries
open GroundTheory.LocalField.EqualChar
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField.EqualChar
theorem _root_.solution : 0 < valuation K (uniformizer K : K) := by
  rw [zero_lt_iff, ne_eq, map_eq_zero]
  exact uniformizer_ne_zero K
end GroundTheory.LocalField.EqualChar
