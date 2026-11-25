-- Prove2me | solution 1 for GlobalTheory.exists_conductor_adicCompletion_of_essFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:53.085268+00:00
-- url     : https://prove2.me/submissions/8311549f-f5c9-4205-bc24-9e26b60534a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRingEquivAdicCompletionLocalizationProdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConductorProdFstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormalLocalIsLocalisationOfFiniteOverPolynomialAStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsRegularLocalRingAdicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RegularLocalRingNormalDomainStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsConductorAdicCompletionEssFiniteType
import Theorems.Thm_GlobalTheory_exists_finite_over_localization_atPrime_below
import Theorems.Thm_GlobalTheory_T_exists_mul_fst_eq_of_integral_of_conductor
import Theorems.Thm_GlobalTheory_T_exists_ne_zero_mul_integral_eq_tensor
import Theorems.Thm_GlobalTheory_T_exists_ringEquiv_adicCompletion_localization_prod
import Theorems.Thm_GlobalTheory_T_injective_and_isLocalization_of_finite_over_mvPolynomial
import Theorems.Thm_GlobalTheory_T_regular_local_ring_normal_domain
import Theorems.Thm_P2M_GlobalTheory_T_isRegularLocalRing_adicCompletion__0bd02646f3a5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], ∃ x : A, x ≠ 0 ∧ ∀ c : FractionRing (AdicCompletion (maximalIdeal A) A), IsIntegral (AdicCompletion (maximalIdeal A) A) c → ∃ s : AdicCompletion (maximalIdeal A) A, algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) s = algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) (algebraMap A (AdicCompletion (maximalIdeal A) A) x) * c := by
  intro A _ _ _ _ _ _
  obtain ⟨r, B, _, _, _, _, _, _, 𝔫, _, hinj, hloc⟩ := GlobalTheory.T.injective_and_isLocalization_of_finite_over_mvPolynomial A
  obtain ⟨p, _, C, _, _, _, _, _, 𝔪, _, hinjC, hlocC, hcomap⟩ :=
    exists_finite_over_localization_atPrime_below (MvPolynomial (Fin r) ℤ) B A 𝔫 hinj
  have hTreg : IsRegularLocalRing (Localization.AtPrime p) := inferInstance
  obtain ⟨_, _⟩ := GlobalTheory.T.regular_local_ring_normal_domain (Localization.AtPrime p)
  have := GlobalTheory.T.isRegularLocalRing_adicCompletion' (Localization.AtPrime p)
  obtain ⟨_, _⟩ := GlobalTheory.T.regular_local_ring_normal_domain
    (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))
  have : CharZero (Localization.AtPrime p) :=
    charZero_of_injective_algebraMap (R := MvPolynomial (Fin r) ℤ)
      (IsLocalization.injective (M := p.primeCompl) (S := Localization.AtPrime p)
        p.primeCompl_le_nonZeroDivisors)
  have hTU : Function.Injective (algebraMap (Localization.AtPrime p)
      (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))) := by
    intro x y h
    exact AdicCompletion.of_injective (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) h
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.T.exists_ne_zero_mul_integral_eq_tensor (Localization.AtPrime p)
    (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) C hTU hinjC
  obtain ⟨S', _, e, he⟩ := GlobalTheory.T.exists_ringEquiv_adicCompletion_localization_prod (Localization.AtPrime p) C A 𝔪 hcomap
  have key := GlobalTheory.T.exists_mul_fst_eq_of_integral_of_conductor (AdicCompletion (maximalIdeal A) A) S' _ e _ hd
  have hed : (e (algebraMap (Localization.AtPrime p) _ d)).1 =
      algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A (algebraMap _ C d)) := by
    rw [Algebra.TensorProduct.algebraMap_apply', he]
  refine ⟨algebraMap C A (algebraMap _ C d), ?_, fun c hc => ?_⟩
  · intro h0
    apply hd0
    apply hinjC
    apply IsLocalization.injective (M := 𝔪.primeCompl) (S := A) 𝔪.primeCompl_le_nonZeroDivisors
    rw [h0, map_zero, map_zero]
  · obtain ⟨s, hs⟩ := key c hc
    exact ⟨s, by rw [hs, hed]⟩
end GlobalTheory
