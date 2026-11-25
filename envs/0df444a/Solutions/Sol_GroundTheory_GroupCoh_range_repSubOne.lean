-- Prove2me | solution 1 for GroundTheory.GroupCoh.range_repSubOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:10:46.248063+00:00
-- url     : https://prove2.me/submissions/8eafb2c0-fde9-4f22-8e06-cbf804e5a2fe

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandRep
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_HerbrandTate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
universe u
open CategoryTheory
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    (repSubOne A σ).range = (Representation.Coinvariants.ker A.ρ).toAddSubgroup := by
  rw [Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ σ hσ]
  ext x
  rw [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  rfl
end GroundTheory.GroupCoh
