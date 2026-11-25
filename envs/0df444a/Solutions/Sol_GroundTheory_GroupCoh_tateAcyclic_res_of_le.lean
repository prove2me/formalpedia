-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateAcyclic_res_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:04:23.932921+00:00
-- url     : https://prove2.me/submissions/3648b851-b523-4a9c-a2ec-67c961355b4e

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialPGroup
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
import Definitions.Def_GroundTheory_TateCohomology_CoresRes
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_res_res_iff

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
theorem _root_.solution {A : Rep.{u} k G} {P : Subgroup G} (hP : CohTrivial (res P.subtype A))
    {V : Subgroup G} [Fintype V] (hV : V ≤ P) : TateAcyclic (res V.subtype A) := by
  classical
  let _ : Fintype (V.subgroupOf P) :=
    Fintype.ofInjective (fun x : V.subgroupOf P => (⟨(x : P), Subgroup.mem_subgroupOf.1 x.2⟩ : V))
      fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun y : V => (y : G)) hab))
  refine (tateAcyclic_res_res_iff A P (V.subgroupOf P) V ?_).1 (hP _)
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hV]
end GroundTheory.GroupCoh
