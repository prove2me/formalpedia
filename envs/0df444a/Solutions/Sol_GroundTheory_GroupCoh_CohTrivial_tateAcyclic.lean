-- Prove2me | solution 1 for GroundTheory.GroupCoh.CohTrivial.tateAcyclic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:06.210949+00:00
-- url     : https://prove2.me/submissions/a1108cdd-412a-4390-8f98-19aa6c6d3559

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
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
namespace CohTrivial
theorem _root_.solution [Fintype G] {A : Rep.{u} k G} (h : CohTrivial A) :
    TateAcyclic A := by
  let _ : Fintype (⊤ : Subgroup G) := Fintype.ofFinite _
  have hbij : Function.Bijective (⊤ : Subgroup G).subtype :=
    ⟨Subgroup.subtype_injective _, fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩⟩
  have h1 : TateAcyclic (res (⊤ : Subgroup G).subtype A) := h ⊤
  exact (tateAcyclic_res_iff _ hbij A).1 h1
end CohTrivial
end GroundTheory.GroupCoh
