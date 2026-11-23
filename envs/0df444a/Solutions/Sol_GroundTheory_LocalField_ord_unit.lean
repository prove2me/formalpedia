-- Prove2me | solution 1 for GroundTheory.LocalField.ord_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:21:29.378813+00:00
-- url     : https://prove2.me/submissions/4b6672ad-d48f-4387-9360-e6a7c3f7bc31

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic

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
open ValuativeRel IsLocalRing
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace GroundTheory.LocalField
theorem _root_.solution (u : 𝒪[K]ˣ) : ord ((u : 𝒪[K]) : K) = 0 := by
  simp [ord, normalizedValuation_unit u]
end GroundTheory.LocalField
