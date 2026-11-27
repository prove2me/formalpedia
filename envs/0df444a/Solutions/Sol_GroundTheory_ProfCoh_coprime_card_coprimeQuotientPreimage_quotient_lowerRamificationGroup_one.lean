-- Prove2me | solution 1 for GroundTheory.ProfCoh.coprime_card_coprimeQuotientPreimage_quotient_lowerRamificationGroup_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:50:48.949683+00:00
-- url     : https://prove2.me/submissions/442f606c-ab68-4b85-a523-9971c7594f39

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
import Theorems.Thm_GroundTheory_ProfCoh_coprime_card_coprimeQuotientPreimage_quotient
import Theorems.Thm_GroundTheory_LocalField_coprime_card_lowerRamificationGroup_zero_quotient
import Theorems.Thm_GroundTheory_LocalField_isCyclic_lowerRamificationGroup_zero_quotient
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
    (Nat.card (coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K]) ⧸
      (lowerRamificationGroup K L 1).subgroupOf
        (coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])))).Coprime
      (ringChar 𝓀[K]) := by
  have := isCyclic_lowerRamificationGroup_zero_quotient K L
  exact coprime_card_coprimeQuotientPreimage_quotient (CharP.char_is_prime 𝓀[K] _) _ _
    (lowerRamificationGroup_antitone K L zero_le_one)
    (coprime_card_lowerRamificationGroup_zero_quotient K L)
end GroundTheory.ProfCoh
