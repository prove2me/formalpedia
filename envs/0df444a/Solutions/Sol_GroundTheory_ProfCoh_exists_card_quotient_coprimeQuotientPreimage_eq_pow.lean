-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_card_quotient_coprimeQuotientPreimage_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:32:40.16854+00:00
-- url     : https://prove2.me/submissions/46d49455-fed6-4b3a-9f96-5303c7fc4e33

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
import Theorems.Thm_GroundTheory_ProfCoh_isPGroup_quotient_coprimeQuotientPreimage

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
variable {G : Type*} [Group G]
variable (N : Subgroup G) [N.Normal]
namespace GroundTheory.ProfCoh
theorem _root_.solution [Finite G] {p : ℕ} (hp : p.Prime) :
    ∃ a : ℕ, Nat.card (G ⧸ coprimeQuotientPreimage N p) = p ^ a := by
  have := Fact.mk hp
  exact IsPGroup.iff_card.1 (isPGroup_quotient_coprimeQuotientPreimage N hp)
end GroundTheory.ProfCoh
