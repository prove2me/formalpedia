-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateIndIso_naturality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:47:15.845263+00:00
-- url     : https://prove2.me/submissions/1232a9ed-7020-49ad-adae-05680f2b4c31

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DiagonalSuccIsoFreeInvSingle
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateShapiro

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
open CategoryTheory Limits groupCohomology groupHomology Rep HomologicalComplex
universe u
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [Fintype G] [Fintype S]
namespace GroundTheory.GroupCoh
theorem _root_.solution {B B' : Rep.{u} k S} (f : B ⟶ B') (n : ℤ) :
    (tateCohomologyFunctor n).map ((indFunctor k S.subtype).map f) ≫ (tateIndIso S B' n).hom =
      (tateIndIso S B n).hom ≫ (tateCohomologyFunctor n).map f :=
  (tateIndNatIso S n).hom.naturality f
end GroundTheory.GroupCoh
