-- Prove2me | solution 1 for GroundTheory.GroupCoh.revHom_naturality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:49:07.633872+00:00
-- url     : https://prove2.me/submissions/0a2df6d3-639c-484e-9506-d7c198d9604c

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_CochainReverse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory Limits groupCohomology
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep k G)
variable {A}
namespace GroundTheory.GroupCoh
theorem _root_.solution {B : Rep k G} (φ : A ⟶ B) :
    revHom A ≫ cochainsMap (MonoidHom.id G) φ = cochainsMap (MonoidHom.id G) φ ≫ revHom B := by
  refine HomologicalComplex.hom_ext _ _ fun n =>
    ModuleCat.hom_ext (LinearMap.ext fun f => funext fun x => ?_)
  change φ.hom (revCochain n f x) = revCochain n (fun y => φ.hom (f y)) x
  rw [revCochain_apply, revCochain_apply, map_smul, Rep.hom_comm_apply]
end GroundTheory.GroupCoh
