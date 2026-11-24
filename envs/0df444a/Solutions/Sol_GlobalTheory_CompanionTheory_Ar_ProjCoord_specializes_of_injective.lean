-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.ProjCoord.specializes_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:20:26.868396+00:00
-- url     : https://prove2.me/submissions/9207845b-df76-46ae-a999-c58c1321dc44

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.ProjCoord
variable {X : Scheme.{0}} {Ω A : Type} [Field Ω] [CommRing A]
namespace GlobalTheory.CompanionTheory.Ar.ProjCoord
theorem _root_.solution (φ : A →+* Ω) (hφ : Function.Injective φ)
    (q : Spec (CommRingCat.of A)) : genPt (CptModel.pt φ) ⤳ q := by
  refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
  change (genPt (CptModel.pt φ)).asIdeal ≤ _
  rw [CptModel.genPt_asIdeal, (RingHom.injective_iff_ker_eq_bot _).1 hφ]
  exact bot_le
end GlobalTheory.CompanionTheory.Ar.ProjCoord
