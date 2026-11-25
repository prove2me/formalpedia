-- Prove2me | solution 1 for GroundTheory.LocalField.isSolvable_lowerRamificationGroup_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:21.706816+00:00
-- url     : https://prove2.me/submissions/ddcf0a2f-11ae-4a70-92a1-e437c8b8a79c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_RamificationUnits
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Theorems.Thm_GroundTheory_LocalField_isPGroup_lowerRamificationGroup_one

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
open ValuativeRel IsLocalRing
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution : Group.IsSolvable (lowerRamificationGroup K L 1) := by
  have : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.char_is_prime 𝓀[K] _⟩
  have := (isPGroup_lowerRamificationGroup_one K L).isNilpotent
  infer_instance
end GroundTheory.LocalField
