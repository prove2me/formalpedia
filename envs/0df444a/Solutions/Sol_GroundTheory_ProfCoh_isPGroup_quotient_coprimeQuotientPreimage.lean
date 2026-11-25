-- Prove2me | solution 1 for GroundTheory.ProfCoh.isPGroup_quotient_coprimeQuotientPreimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:24:44.842558+00:00
-- url     : https://prove2.me/submissions/046271fd-733b-4e5c-8473-7bae76e4cd6b

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
import Theorems.Thm_GroundTheory_ProfCoh_exists_pow_prime_pow_mem_coprimePart

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
    IsPGroup p (G ⧸ coprimeQuotientPreimage N p) := by
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨k, hk⟩ :=
    exists_pow_prime_pow_mem_coprimePart hp (isOfFinOrder_of_finite (QuotientGroup.mk' N g))
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, coprimeQuotientPreimage,
    Subgroup.mem_comap, map_pow]
  exact hk
end GroundTheory.ProfCoh
