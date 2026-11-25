-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordModel.not_coordTie_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:19.142147+00:00
-- url     : https://prove2.me/submissions/e36c98ef-4741-4cb9-82aa-cb3c0c836319

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie

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
theorem _root_.solution (o : Type) [CommRing o] [Algebra o Ω] {κ : Type} : ¬ CoordTie o ξ (0 : κ → Ω) := by
  intro h
  obtain ⟨c, hc⟩ := h.cover ⟨genPt ξ, specializes_rfl⟩
  exact hc.1 rfl
end GlobalTheory.CompanionTheory.Ar.CoordModel
