-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_card_quotient_coprimeQuotientPreimage_lowerRamificationGroup_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:51:02.346254+00:00
-- url     : https://prove2.me/submissions/9198a625-5e80-4c7c-a4fd-d84f3eb9d7ab

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
import Theorems.Thm_GroundTheory_ProfCoh_exists_card_quotient_coprimeQuotientPreimage_eq_pow

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
    ∃ a : ℕ, Nat.card ((L ≃ₐ[K] L) ⧸
      coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) =
        ringChar 𝓀[K] ^ a :=
  exists_card_quotient_coprimeQuotientPreimage_eq_pow _ (CharP.char_is_prime 𝓀[K] _)
end GroundTheory.ProfCoh
