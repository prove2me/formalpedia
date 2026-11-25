-- Prove2me | solution 1 for GroundTheory.GroupCoh.CohTrivial.of_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:22:10.122962+00:00
-- url     : https://prove2.me/submissions/24405d9c-c6c1-458a-85e7-dd7ee95e89da

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
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
open CategoryTheory Limits Rep
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [CommRing k] [Group G]
namespace GroundTheory.GroupCoh
namespace CohTrivial
theorem _root_.solution {M N : Rep.{u} k G} (i : M ⟶ N) (r : N ⟶ M) (h : i ≫ r = 𝟙 M)
    (hN : CohTrivial N) : CohTrivial M := fun S _ =>
  (hN S).of_retract ((resFunctor S.subtype).map i) ((resFunctor S.subtype).map r)
    (by rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id])
end CohTrivial
end GroundTheory.GroupCoh
