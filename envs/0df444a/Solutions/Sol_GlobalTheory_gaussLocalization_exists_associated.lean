-- Prove2me | solution 1 for GlobalTheory.gaussLocalization_exists_associated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:58:58.428802+00:00
-- url     : https://prove2.me/submissions/289398f4-3c19-4b28-a599-7b1b34af9e1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPolynomialMapMaximalIdealIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingOfFlatOfFormallyUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
import Theorems.Thm_GlobalTheory_mvPolynomial_exists_content


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O] [ValuationRing O]
    (g : ℕ) (p : Ideal (MvPolynomial (Fin g) O)) [p.IsPrime]
    (hp : p = (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O))
    (w : Localization.AtPrime p) (hw : w ≠ 0) :
    ∃ π : O, Associated w (algebraMap _ (Localization.AtPrime p)
      (MvPolynomial.C π : MvPolynomial (Fin g) O)) := by
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl w
  have ha : a ≠ 0 := by
    rintro rfl
    exact hw (IsLocalization.mk'_zero _)
  obtain ⟨π, F, rfl, hF⟩ := mvPolynomial_exists_content O g a ha
  refine ⟨π, ?_⟩
  rw [← hp] at hF
  have hu : IsUnit (IsLocalization.mk' (Localization.AtPrime p) F u) :=
    (IsLocalization.AtPrime.isUnit_mk'_iff _ p F u).2 hF
  simp only
  rw [← IsLocalization.mul_mk'_eq_mk'_of_mul]
  exact (associated_mul_unit_left _ _ hu)
end GlobalTheory
