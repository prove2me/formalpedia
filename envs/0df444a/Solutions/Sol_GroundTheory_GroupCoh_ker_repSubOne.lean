-- Prove2me | solution 1 for GroundTheory.GroupCoh.ker_repSubOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:09.476542+00:00
-- url     : https://prove2.me/submissions/b962872b-861d-4108-95c5-4213a6e81b6f

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandRep
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_HerbrandTate
import Theorems.Thm_GroundTheory_GroupCoh_repSubOne_apply


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
omit [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    (repSubOne A σ).ker = A.ρ.invariants.toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, repSubOne_apply, sub_eq_zero, Submodule.mem_toAddSubgroup,
    Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ σ hσ]
end GroundTheory.GroupCoh
