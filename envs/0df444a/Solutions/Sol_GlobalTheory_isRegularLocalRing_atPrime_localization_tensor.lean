-- Prove2me | solution 1 for GlobalTheory.isRegularLocalRing_atPrime_localization_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:16:11.146023+00:00
-- url     : https://prove2.me/submissions/646cb288-7e44-43dc-9d9b-40fbb851f320

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularLocalRingAtPrimeLocalizationTensor
import Theorems.Thm_GlobalTheory_isRegularLocalRing_atPrime_of_ringEquiv_isLocalization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (r : ℕ) (𝔪 : Ideal (MvPolynomial (Fin r) k)) [𝔪.IsPrime] (𝔫 : Ideal (Localization.AtPrime 𝔪 ⊗[k] K)) [𝔫.IsPrime], IsRegularLocalRing (Localization.AtPrime 𝔫) := by
  intro k K _ _ _ r 𝔪 _ 𝔫 _
  letI : Algebra (MvPolynomial (Fin r) k ⊗[k] K)
      (Localization.AtPrime 𝔪 ⊗[MvPolynomial (Fin r) k] (MvPolynomial (Fin r) k ⊗[k] K)) :=
    Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin r) k ⊗[k] K) 𝔪.primeCompl)
      (Localization.AtPrime 𝔪 ⊗[MvPolynomial (Fin r) k] (MvPolynomial (Fin r) k ⊗[k] K)) :=
    IsLocalization.tensorRight (Localization.AtPrime 𝔪) 𝔪.primeCompl
  let h : (MvPolynomial (Fin r) k ⊗[k] K) ≃+* MvPolynomial (Fin r) K :=
    (Algebra.TensorProduct.comm k (MvPolynomial (Fin r) k) K).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv k K).toRingEquiv
  haveI := IsLocalization.isLocalization_of_base_ringEquiv
    (Algebra.algebraMapSubmonoid (MvPolynomial (Fin r) k ⊗[k] K) 𝔪.primeCompl)
    (Localization.AtPrime 𝔪 ⊗[MvPolynomial (Fin r) k] (MvPolynomial (Fin r) k ⊗[k] K)) h
  letI : Algebra (MvPolynomial (Fin r) K)
      (Localization.AtPrime 𝔪 ⊗[MvPolynomial (Fin r) k] (MvPolynomial (Fin r) k ⊗[k] K)) :=
    ((algebraMap (MvPolynomial (Fin r) k ⊗[k] K) _).comp h.symm.toRingHom).toAlgebra
  exact isRegularLocalRing_atPrime_of_ringEquiv_isLocalization
    (Submonoid.map h (Algebra.algebraMapSubmonoid (MvPolynomial (Fin r) k ⊗[k] K) 𝔪.primeCompl))
    (Algebra.TensorProduct.cancelBaseChange k (MvPolynomial (Fin r) k) (Localization.AtPrime 𝔪)
      (Localization.AtPrime 𝔪) K).symm.toRingEquiv 𝔫
end GlobalTheory
