-- Prove2me | solution 1 for GlobalTheory.T.smooth_algebra_localization_eq_zero_of_avoid_fibre_minimal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:22:07.7004+00:00
-- url     : https://prove2.me/submissions/e25cbcdd-64e2-4140-86bd-6aba06ba089c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinimStatement
import Theorems.Thm_GlobalTheory_FlatFibreRegular_localization_eq_zero_of_mul_eq_zero


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
theorem _root_.solution : ∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  first | exact @GlobalTheory.FlatFibreRegular.localization_eq_zero_of_mul_eq_zero | exact GlobalTheory.FlatFibreRegular.localization_eq_zero_of_mul_eq_zero | (intros; apply GlobalTheory.FlatFibreRegular.localization_eq_zero_of_mul_eq_zero <;> assumption)
end _root_.GlobalTheory.T
