-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateCores_naturality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:47:11.228205+00:00
-- url     : https://prove2.me/submissions/e8b88dcb-4ae8-4604-940f-b091d8acaa4f

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
    (resFunctor S.subtype ⋙ tateCohomologyFunctor n).map f ≫ (tateCores S n).app B =
      (tateCores S n).app A ≫ (tateCohomologyFunctor n).map f :=
  (tateCores S n).naturality f
end GroundTheory.GroupCoh
