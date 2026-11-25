-- Prove2me | solution 1 for GlobalTheory.reducePoint_residue_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:58.081161+00:00
-- url     : https://prove2.me/submissions/7b0774db-7491-4318-85f7-318fc0fdf9bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Theorems.Thm_GlobalTheory_reducePoint_quotient_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (B : Type u) [CommRing B] [HenselianLocalRing B] (s : Spec (.of B) ⟶ S)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (B : Type u) [CommRing B] [HenselianLocalRing B] (s : Spec (.of B) ⟶ S)
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution [Smooth f] :
    Function.Surjective (_root_.GlobalTheory.reducePoint f (CommRingCat.ofHom (residue B)) s) :=
  _root_.GlobalTheory.reducePoint_quotient_surjective f B (maximalIdeal B) s
end _root_.GlobalTheory
end GlobalTheory
