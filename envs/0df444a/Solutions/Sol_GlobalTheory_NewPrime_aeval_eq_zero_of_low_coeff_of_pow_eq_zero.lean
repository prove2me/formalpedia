-- Prove2me | solution 1 for GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:08:31.843463+00:00
-- url     : https://prove2.me/submissions/d1d30ca1-5dbf-4429-89f7-00bb4a5d42e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalEqZeroOfLowCoeffOfNilpotentMultiple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NewPrime
namespace GlobalTheory.NewPrime
theorem _root_.solution :
    ∀ (O B : Type) [CommRing O] [CommRing B] [Algebra O B] (ι : Type) (t : B) (K : ℕ) (ξ : ι → B)
      (F : MvPolynomial ι O), t ^ K = 0 → (∀ q, t ∣ ξ q) →
      (∀ u : ι →₀ ℕ, u.degree < K → algebraMap O B (F.coeff u) = 0) →
      MvPolynomial.aeval ξ F = 0 := by
  intro O B _ _ _ ι t K ξ F htK hdvd hlow
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Finset.sum_eq_zero fun u _ => ?_
  by_cases hu : u.degree < K
  · rw [hlow u hu, zero_mul]
  ·
    have hmon : t ^ u.degree ∣ ∏ i ∈ u.support, ξ i ^ u i := by
      rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => pow_dvd_pow_of_dvd (hdvd i) _
    have hK : t ^ K ∣ ∏ i ∈ u.support, ξ i ^ u i :=
      (pow_dvd_pow t (not_lt.mp hu)).trans hmon
    rw [htK, zero_dvd_iff] at hK
    rw [hK, mul_zero]
end GlobalTheory.NewPrime
