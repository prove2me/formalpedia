-- Prove2me | solution 1 for GroundTheory.LocalField.normalizedValuation_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:15.185617+00:00
-- url     : https://prove2.me/submissions/deb2b631-5f8e-4df9-b118-9bbe48004d61

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
theorem _root_.solution {x : K} :
    normalizedValuation K x ≤ 1 ↔ x ∈ 𝒪[K] := by
  rw [← map_one (normalizedValuation K), normalizedValuation_le_iff, map_one]
  exact (Valuation.mem_integer_iff _ _).symm
end GroundTheory.LocalField
