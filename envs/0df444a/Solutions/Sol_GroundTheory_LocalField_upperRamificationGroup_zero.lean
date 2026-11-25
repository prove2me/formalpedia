-- Prove2me | solution 1 for GroundTheory.LocalField.upperRamificationGroup_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:39:47.556814+00:00
-- url     : https://prove2.me/submissions/ace5cb6d-a7bc-4d35-8cba-1e93fe9888c5

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
import Theorems.Thm_GroundTheory_LocalField_upperRamificationGroup_of_nonpos

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
open ValuativeRel Filter Topology MeasureTheory
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
namespace GroundTheory.LocalField
theorem _root_.solution :
    upperRamificationGroup K L 0 = lowerRamificationGroup K L 0 := by
  rw [upperRamificationGroup_of_nonpos le_rfl, ← Nat.cast_zero, lowerRamificationGroupReal_natCast,
    Nat.cast_zero]
end GroundTheory.LocalField
