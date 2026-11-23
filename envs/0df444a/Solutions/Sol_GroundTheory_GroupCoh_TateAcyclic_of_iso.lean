-- Prove2me | solution 1 for GroundTheory.GroupCoh.TateAcyclic.of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:07:23.754209+00:00
-- url     : https://prove2.me/submissions/b8a19bc3-ab82-4b36-924e-920be232ac79

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_retract

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
open CategoryTheory Limits groupCohomology groupHomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
namespace TateAcyclic
theorem _root_.solution {M N : Rep.{u} k G} (e : M ≅ N) (hN : TateAcyclic N) :
    TateAcyclic M :=
  hN.of_retract e.hom e.inv e.hom_inv_id
end TateAcyclic
end GroundTheory.GroupCoh
