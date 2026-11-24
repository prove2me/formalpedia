-- Prove2me | solution 1 for GlobalTheory.bijective_restrictPoints_of_etale_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:56:42.234898+00:00
-- url     : https://prove2.me/submissions/d8f3d66b-2630-4ce8-9389-29f30ec966d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Theorems.Thm_GlobalTheory_existsUnique_lift_of_etale_of_henselian
import Theorems.Thm_GlobalTheory_bijective_restrictPoints_of_existsUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    (R : Type u) [CommRing R] [HenselianLocalRing R] (h : Spec (.of R) ⟶ S) :
    Function.Bijective (restrictPoints f h
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) :=
  bijective_restrictPoints_of_existsUnique f h _ fun g w ↦
    existsUnique_lift_of_etale_of_henselian f _ IsLocalRing.residue_surjective g h w
end GlobalTheory
