-- Prove2me | solution 1 for GroundTheory.LocalField.ord_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:51.368077+00:00
-- url     : https://prove2.me/submissions/e5767893-8a0a-4571-8161-437c609abfa3

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
theorem _root_.solution {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) : ord (ϖ : K) = 1 := by
  simp [ord, normalizedValuation_uniformizer hϖ]
end GroundTheory.LocalField
