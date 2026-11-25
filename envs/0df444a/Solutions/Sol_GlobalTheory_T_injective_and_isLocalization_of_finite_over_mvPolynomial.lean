-- Prove2me | solution 1 for GlobalTheory.T.injective_and_isLocalization_of_finite_over_mvPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:16:13.881311+00:00
-- url     : https://prove2.me/submissions/41e4d7a9-44ca-43c7-b133-0788699cde81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormalLocalIsLocalisationOfFiniteOverPolynomialA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormalLocalIsLocalisationOfFiniteOverPolynomialAStatement
import Theorems.Thm_GlobalTheory_normal_local_is_localisation_of_finite_over_polynomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], ∃ (r : ℕ) (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsIntegrallyClosed B) (_ : Algebra (MvPolynomial (Fin r) ℤ) B) (_ : Module.Finite (MvPolynomial (Fin r) ℤ) B) (_ : Algebra B A) (𝔫 : Ideal B) (_ : 𝔫.IsPrime), Function.Injective (algebraMap (MvPolynomial (Fin r) ℤ) B) ∧ IsLocalization.AtPrime A 𝔫 := by
  first | exact @GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial | exact GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial | (intros; apply GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial <;> assumption)
end _root_.GlobalTheory.T
