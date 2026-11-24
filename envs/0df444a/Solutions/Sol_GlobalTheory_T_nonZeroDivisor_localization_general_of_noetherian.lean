-- Prove2me | solution 1 for GlobalTheory.T.nonZeroDivisor_localization_general_of_noetherian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:03.530907+00:00
-- url     : https://prove2.me/submissions/98723167-431a-418f-a861-fc0c8c47860a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonZeroDivisorLocalizationGeneralOfNoetherian
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonZeroDivisorLocalizationGeneralOfNoetherianStatement
import Theorems.Thm_GlobalTheory_NzdDescent_of_noetherian


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : (∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0) →
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  first | exact @GlobalTheory.NzdDescent.of_noetherian | exact GlobalTheory.NzdDescent.of_noetherian | (intros; apply GlobalTheory.NzdDescent.of_noetherian <;> assumption)
end _root_.GlobalTheory.T
