-- Prove2me | solution 1 for GlobalTheory.exists_poly_sub_mem_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:41:15.552383+00:00
-- url     : https://prove2.me/submissions/326a5522-20cb-441c-a8de-e4756ebfaaa2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolynomialApproxPowMaximal
import Theorems.Thm_P2M_GlobalTheory_exists_eval__approx_maximalIdeal_pow_succ_b703603b90f8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {A R : Type} [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (φ : A →+* R), (maximalIdeal A).map φ = maximalIdeal R →
    ∀ θ : R, (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) →
    ∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n := by
  intro A R _ _ _ _ φ hm θ h1 n r
  simp only [Polynomial.eval_map] at h1 ⊢
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨P, hP⟩ := ih
    obtain ⟨Q, -, hQ⟩ := exists_eval₂_approx_maximalIdeal_pow_succ φ hm θ h1 n _ hP
    refine ⟨P + Q, ?_⟩
    have : r - Polynomial.eval₂ φ θ (P + Q) =
        r - Polynomial.eval₂ φ θ P - Polynomial.eval₂ φ θ Q := by
      rw [Polynomial.eval₂_add]; ring
    rw [this]; exact hQ
end GlobalTheory
