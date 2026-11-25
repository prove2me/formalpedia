-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateRes_app_comp_tateCores_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:38.401794+00:00
-- url     : https://prove2.me/submissions/659074c9-a67a-4e1f-af3f-a9e7bff935ea

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_CoresRes
import Theorems.Thm_GroundTheory_GroupCoh_unit_comp_indCoindIso_inv_comp_counit
import Theorems.Thm_GroundTheory_GroupCoh_tateIndIso_inv_eq
import Theorems.Thm_GroundTheory_GroupCoh_tateCores_app
import Theorems.Thm_GroundTheory_GroupCoh_tateRes_app


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
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable [Fintype G] (S : Subgroup G) [Fintype S]
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep.{u} k G) (n : ℤ) :
    (tateRes S n).app A ≫ (tateCores S n).app A = S.index • 𝟙 (tateCohomology A n) := by
  rw [tateRes_app, tateCores_app, tateIndIso_inv_eq, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, ← Functor.map_comp, ← Functor.map_comp,
    unit_comp_indCoindIso_inv_comp_counit, Functor.map_nsmul]
  exact congrArg (S.index • ·) ((tateCohomologyFunctor n).map_id A)
end GroundTheory.GroupCoh
