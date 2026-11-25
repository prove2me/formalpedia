-- Prove2me | solution 1 for GroundTheory.ProfCoh.coprime_card_quotient_primaryQuotientPreimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:12.172448+00:00
-- url     : https://prove2.me/submissions/f6a3abfe-f6bb-49d4-b3ea-73d19489801e

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
import Theorems.Thm_GroundTheory_ProfCoh_exists_coprime_pow_mem_primaryPart
import Theorems.Thm_GroundTheory_ProfCoh_mem_of_pow_mem_of_pow_mem
import Theorems.Thm_GroundTheory_ProfCoh_coprime_card_of_pow_eq_one

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
theorem _root_.solution [Finite G] {l : ℕ} (hl : l.Prime) :
    (Nat.card (G ⧸ primaryQuotientPreimage N l)).Coprime l := by
  have := Fact.mk hl
  apply coprime_card_of_pow_eq_one
  intro y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, primaryQuotientPreimage,
    Subgroup.mem_comap, map_pow] at hy
  rw [QuotientGroup.eq_one_iff, primaryQuotientPreimage, Subgroup.mem_comap]
  obtain ⟨m, hm, hgm⟩ :=
    exists_coprime_pow_mem_primaryPart hl (isOfFinOrder_of_finite (QuotientGroup.mk' N g))
  exact mem_of_pow_mem_of_pow_mem hm.symm hy hgm
end GroundTheory.ProfCoh
