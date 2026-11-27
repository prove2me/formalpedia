-- Prove2me | solution 1 for GroundTheory.ProfCoh.isCyclic_quotient_coprimeQuotientPreimage_lowerRamificationGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:48:59.915813+00:00
-- url     : https://prove2.me/submissions/568b0f24-14dc-4833-8185-24b7d6ccdba2

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
import Theorems.Thm_GroundTheory_ProfCoh_isCyclic_quotient_of_le
import Theorems.Thm_GroundTheory_ProfCoh_le_coprimeQuotientPreimage

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
    IsCyclic ((L ≃ₐ[K] L) ⧸
      coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) :=
  isCyclic_quotient_of_le (le_coprimeQuotientPreimage _ _)
end GroundTheory.ProfCoh
