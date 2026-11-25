-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateCohomologyFunctor_map_tateZeroClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:14:34.754914+00:00
-- url     : https://prove2.me/submissions/dc4102e2-24de-4b61-b08a-b619f4bd21da

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
import Theorems.Thm_GroundTheory_GroupCoh_homologyMap_tateZeroClass

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
open CategoryTheory Limits Rep groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution {M N : Rep.{u} k G} (φ : M ⟶ N)
    (x : M.ρ.invariants) :
    ((tateCohomologyFunctor 0).map φ).hom (tateZeroClass M x) =
      tateZeroClass N (((Rep.invariantsFunctor k G).map φ).hom x) :=
  homologyMap_tateZeroClass (tateComplex.map φ) x _ (funext fun _ => rfl)
end GroundTheory.GroupCoh
