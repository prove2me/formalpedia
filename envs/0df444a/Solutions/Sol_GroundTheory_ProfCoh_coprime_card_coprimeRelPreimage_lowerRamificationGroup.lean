-- Prove2me | solution 1 for GroundTheory.ProfCoh.coprime_card_coprimeRelPreimage_lowerRamificationGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:50:54.798099+00:00
-- url     : https://prove2.me/submissions/5f3f6c87-2e6a-4c40-8276-8e0475faa93f

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
import Theorems.Thm_GroundTheory_ProfCoh_coprime_card_coprimeRelPreimage
import Theorems.Thm_GroundTheory_LocalField_isCyclic_lowerRamificationGroup_zero_quotient
import Theorems.Thm_GroundTheory_LocalField_isPGroup_lowerRamificationGroup_one


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
theorem _root_.solution {l : ℕ} (hl : l.Prime)
    (hlp : l ≠ ringChar 𝓀[K]) :
    (Nat.card (coprimeRelPreimage (lowerRamificationGroup K L 0)
      (lowerRamificationGroup K L 1) l)).Coprime l := by
  have := isCyclic_lowerRamificationGroup_zero_quotient K L
  exact coprime_card_coprimeRelPreimage _ _ hl (CharP.char_is_prime 𝓀[K] _) hlp
    (isPGroup_lowerRamificationGroup_one K L)
end GroundTheory.ProfCoh
