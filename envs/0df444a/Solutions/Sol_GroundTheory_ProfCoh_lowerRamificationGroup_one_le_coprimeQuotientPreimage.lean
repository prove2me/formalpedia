-- Prove2me | solution 1 for GroundTheory.ProfCoh.lowerRamificationGroup_one_le_coprimeQuotientPreimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:49:19.792033+00:00
-- url     : https://prove2.me/submissions/1120194c-4982-4c5d-aef5-d37f4530452d

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
import Theorems.Thm_GroundTheory_ProfCoh_le_coprimeQuotientPreimage
import Theorems.Thm_GroundTheory_LocalField_lowerRamificationGroup_antitone


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.LocalField ValuativeRel IntermediateField
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.ProfCoh
theorem _root_.solution :
    lowerRamificationGroup K L 1 ≤
      coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K]) :=
  (lowerRamificationGroup_antitone K L zero_le_one).trans (le_coprimeQuotientPreimage _ _)
end GroundTheory.ProfCoh
