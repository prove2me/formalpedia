-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermitianForm.pairing_eq_zero_of_psd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:55:12.073296+00:00
-- url     : https://prove2.me/submissions/0d711524-688d-493a-b546-4b7cdc152984

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianPsdIsotropicRadical
import Theorems.Thm_GlobalTheory_CompanionTheory_HermitianForm_re_pairing_eq_zero_of_psd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermitianForm
namespace GlobalTheory.CompanionTheory.HermitianForm
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v w, B w v = starRingEnd ℂ (B v w)) →
    (∀ v, 0 ≤ (B v v).re) → ∀ v, B v v = 0 → ∀ w, B v w = 0 := by
  intro V _ _ B hB hpos v hv w
  have hre := re_pairing_eq_zero_of_psd B hB hpos v hv w
  have him := re_pairing_eq_zero_of_psd B hB hpos v hv (Complex.I • w)
  have e : B v (Complex.I • w) = -Complex.I * B v w := by
    simp only [map_smulₛₗ, smul_eq_mul, Complex.conj_I]
  rw [e] at him
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at him
  apply Complex.ext
  · simpa using hre
  · simpa using him
end GlobalTheory.CompanionTheory.HermitianForm
