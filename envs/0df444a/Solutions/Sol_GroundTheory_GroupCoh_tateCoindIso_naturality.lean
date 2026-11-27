-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateCoindIso_naturality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:48:23.648143+00:00
-- url     : https://prove2.me/submissions/a498d1cc-9578-4ad7-a85a-fd3dcce063f1

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
    (tateCohomologyFunctor n).map (coindMap S.subtype f) ≫ (tateCoindIso S B' n).hom =
      (tateCoindIso S B n).hom ≫ (tateCohomologyFunctor n).map f :=
  (tateCoindNatIso S n).hom.naturality f
end GroundTheory.GroupCoh
