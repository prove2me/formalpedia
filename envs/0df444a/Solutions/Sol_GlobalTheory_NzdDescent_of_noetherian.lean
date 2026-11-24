-- Prove2me | solution 1 for GlobalTheory.NzdDescent.of_noetherian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:16:54.421281+00:00
-- url     : https://prove2.me/submissions/61ccfb2a-6435-44ca-a4a3-0ef48afbb106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreGoingDownTensorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonZeroDivisorLocalizationGeneralOfNoetherian
import Theorems.Thm_GlobalTheory_NzdDescent_model_data
import Theorems.Thm_GlobalTheory_NzdDescent_of_model

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.NzdDescent
open TensorProduct GlobalTheory.SmoothDescent
namespace GlobalTheory.NzdDescent
theorem _root_.solution : (∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0) →
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  intro hN A B _ _ _ _ b g u hgb hmin
  obtain ⟨S, B₁, _, _, _, _, _, _, e, b₁, g₁, hinj, hb, hg⟩ := model_data A B b g
  exact of_model hN A B S B₁ b g e b₁ g₁ hinj hb hg u hgb hmin
end GlobalTheory.NzdDescent
