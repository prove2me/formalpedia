-- Prove2me | solution 1 for GroundTheory.GroupCoh.CohTrivial.of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:58:32.202522+00:00
-- url     : https://prove2.me/submissions/82216dfa-475b-4ef1-a878-c1a6664a82b5

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Theorems.Thm_GroundTheory_GroupCoh_CohTrivial_of_retract
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
theorem _root_.solution {M N : Rep.{u} k G} (e : M ≅ N) (hN : CohTrivial N) : CohTrivial M :=
  hN.of_retract e.hom e.inv e.hom_inv_id
end CohTrivial
end GroundTheory.GroupCoh
