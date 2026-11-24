-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CptModel.injective_of_isCptGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:34:40.264703+00:00
-- url     : https://prove2.me/submissions/71eab76b-8edb-4b52-9226-57737620ed45

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_eq_of_specializes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CptModel
open AlgebraicGeometry CategoryTheory
variable {R K : Type} [CommRing R] [Field K]
namespace GlobalTheory.CompanionTheory.Ar.CptModel
theorem _root_.solution [IsDomain R] (φ : R →+* K) (h : IsCptGen (pt φ)) :
    Function.Injective φ := by
  have hb : (⊥ : PrimeSpectrum R) ⤳ (genPt (pt φ) : PrimeSpectrum R) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  have e := eq_of_specializes h hb
  rw [RingHom.injective_iff_ker_eq_bot, ← genPt_asIdeal, ← e]
  rfl
end GlobalTheory.CompanionTheory.Ar.CptModel
