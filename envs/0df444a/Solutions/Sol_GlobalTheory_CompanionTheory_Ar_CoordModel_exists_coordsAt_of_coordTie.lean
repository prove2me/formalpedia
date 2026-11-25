-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordModel.exists_coordsAt_of_coordTie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:01.038808+00:00
-- url     : https://prove2.me/submissions/65105d0c-a164-4fff-9c4f-4ad43fca983d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_exists_coordsAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CoordModel
open AlgebraicGeometry CategoryTheory
variable (A : Type) [CommRing A] (Ω : Type) [Field Ω] [Algebra A Ω]
variable [IsDomain A] [IsFractionRing A Ω]
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R] [IsLocalRing R]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of R) ⟶ X}
namespace GlobalTheory.CompanionTheory.Ar.CoordModel
theorem _root_.solution {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (h : CoordTie o ξ x) (hz : genPt ξ ⤳ centre z) :
    ∃ w, CoordsAt ξ (K := Unit) (ι := fun _ => κ) (fun j => x j.2) z w :=
  exists_coordsAt _ hz (fun _ => h.cover _) h.gen
end GlobalTheory.CompanionTheory.Ar.CoordModel
