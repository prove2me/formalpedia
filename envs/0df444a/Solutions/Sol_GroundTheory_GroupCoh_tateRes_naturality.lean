-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateRes_naturality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:47:26.60963+00:00
-- url     : https://prove2.me/submissions/1b196226-2794-4292-8fff-2c1db35be09e

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateShapiro
import Definitions.Def_GroundTheory_TateCohomology_ResCores

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
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]
namespace GroundTheory.GroupCoh
theorem _root_.solution {A B : Rep.{u} k G} (f : A ⟶ B) (n : ℤ) :
    (tateCohomologyFunctor n).map f ≫ (tateRes S n).app B =
      (tateRes S n).app A ≫ (resFunctor S.subtype ⋙ tateCohomologyFunctor n).map f :=
  (tateRes S n).naturality f
end GroundTheory.GroupCoh
