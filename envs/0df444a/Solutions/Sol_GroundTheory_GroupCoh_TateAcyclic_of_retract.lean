-- Prove2me | solution 1 for GroundTheory.GroupCoh.TateAcyclic.of_retract
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:06.376589+00:00
-- url     : https://prove2.me/submissions/1a054860-1597-4154-8c1c-e98d03cb3bc0

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced

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
theorem _root_.solution {M N : Rep.{u} k G} (i : M ⟶ N) (r : N ⟶ M) (h : i ≫ r = 𝟙 M)
    (hN : TateAcyclic N) : TateAcyclic M := fun n => by
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 ((tateCohomologyFunctor n).obj M) = 0
  rw [← (tateCohomologyFunctor n).map_id, ← h, Functor.map_comp,
    (hN n).eq_of_tgt ((tateCohomologyFunctor n).map i) 0, zero_comp]
end TateAcyclic
end GroundTheory.GroupCoh
