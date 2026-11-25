-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateAcyclic_res_res_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:03:21.96837+00:00
-- url     : https://prove2.me/submissions/57429a6b-baab-4501-b742-9f38198faa89

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialPGroup
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
import Definitions.Def_GroundTheory_TateCohomology_CoresRes
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Theorems.Thm_GroundTheory_GroupCoh_res_res
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_res_iff


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
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep.{u} k G) (S : Subgroup G) (T : Subgroup S) [Fintype T]
    (U : Subgroup G) [Fintype U] (hU : T.map S.subtype = U) :
    TateAcyclic (res T.subtype (res S.subtype A)) ↔ TateAcyclic (res U.subtype A) := by
  subst hU
  let U := T.map S.subtype
  let φ : T →* U := (S.subtype.comp T.subtype).codRestrict U fun t =>
    Subgroup.mem_map.2 ⟨t, t.2, rfl⟩
  have hinj : Function.Injective φ := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun x : U => (x : G)) hab))
  have hsurj : Function.Surjective φ := by
    rintro ⟨u, hu⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hu
    exact ⟨⟨x, hx⟩, rfl⟩
  rw [← tateAcyclic_res_iff φ ⟨hinj, hsurj⟩ (res U.subtype A)]
  have e : U.subtype.comp φ = S.subtype.comp T.subtype := rfl
  rw [res_res φ U.subtype A, e, res_res]
end GroundTheory.GroupCoh
