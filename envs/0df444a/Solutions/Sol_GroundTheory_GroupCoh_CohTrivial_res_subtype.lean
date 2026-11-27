-- Prove2me | solution 1 for GroundTheory.GroupCoh.CohTrivial.res_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:46:27.583212+00:00
-- url     : https://prove2.me/submissions/c2c486a0-8e58-4452-802e-0d9db9d86db6

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_res_iff
import Theorems.Thm_GroundTheory_GroupCoh_res_res

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
namespace CohTrivial
theorem _root_.solution {A : Rep.{u} k G} (h : CohTrivial A) (S : Subgroup G) :
    CohTrivial (res S.subtype A) := by
  classical
  intro T _
  let U : Subgroup G := T.map S.subtype
  let φ : T →* U := (S.subtype.comp T.subtype).codRestrict U fun t =>
    Subgroup.mem_map.2 ⟨t, t.2, rfl⟩
  have hinj : Function.Injective φ := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun x : U => (x : G)) hab))
  have hsurj : Function.Surjective φ := by
    rintro ⟨u, hu⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hu
    exact ⟨⟨x, hx⟩, rfl⟩
  let _ : Fintype U := Fintype.ofSurjective φ hsurj
  have hφ := (tateAcyclic_res_iff φ ⟨hinj, hsurj⟩ (Rep.res U.subtype A)).2 (h U)
  have e : U.subtype.comp φ = S.subtype.comp T.subtype := rfl
  rw [res_res, e, ← res_res] at hφ
  exact hφ
end CohTrivial
end GroundTheory.GroupCoh
