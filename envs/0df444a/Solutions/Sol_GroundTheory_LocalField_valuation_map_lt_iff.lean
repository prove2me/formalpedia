-- Prove2me | solution 1 for GroundTheory.LocalField.valuation_map_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:25:37.88545+00:00
-- url     : https://prove2.me/submissions/8b2183c0-b603-45a4-8881-fb9241195beb

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Theorems.Thm_GroundTheory_LocalField_vlt_map_iff

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
variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M]
namespace GroundTheory.LocalField
theorem _root_.solution (f : L →ₐ[K] M) (x y : L) :
    valuation M (f x) < valuation M (f y) ↔ valuation L x < valuation L y := by
  rw [← (valuation M).vlt_iff_lt, ← (valuation L).vlt_iff_lt, vlt_map_iff]
end GroundTheory.LocalField
