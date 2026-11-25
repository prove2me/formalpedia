-- Prove2me | solution 1 for GlobalTheory.exists_forms_algebraicIndependent_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:26.93589+00:00
-- url     : https://prove2.me/submissions/fb6b1635-fa59-4179-b7ae-33823ee16147

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Theorems.Thm_GlobalTheory_exists_forms_idealOfVars_le_radical
import Theorems.Thm_GlobalTheory_exists_forms_sub_sum_mem
import Theorems.Thm_GlobalTheory_finite_aeval_of_forms_eq_sum
import Theorems.Thm_GlobalTheory_injective_of_finite_of_ringKrullDim_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ : Type*} [Finite σ] {k : Type*} [Field k]
namespace GlobalTheory
theorem _root_.solution {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) {δ : ℕ}
    (hdim : ringKrullDim (MvPolynomial σ k ⧸ I) = δ) :
    ∃ (e d₀ : ℕ) (F : Fin δ → MvPolynomial σ k), 1 ≤ e ∧ e ≤ d₀ ∧
      (∀ i, (F i).IsHomogeneous e) ∧
      AlgebraicIndependent k (fun i => Ideal.Quotient.mk I (F i)) ∧
      (∀ d, d₀ ≤ d → ∀ p : MvPolynomial σ k, p.IsHomogeneous d →
        ∃ G : Fin δ → MvPolynomial σ k,
          (∀ i, (G i).IsHomogeneous (d - e)) ∧ p - ∑ i, F i * G i ∈ I) ∧
      (aeval (fun i => Ideal.Quotient.mk I (F i)) :
        MvPolynomial (Fin δ) k →ₐ[k] MvPolynomial σ k ⧸ I).Finite := by
  have hI' : I ≠ ⊤ := by
    rintro rfl
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (WithBot.bot_ne_coe (a := (δ : ℕ∞)))
  obtain ⟨e, he, F, hF, hle⟩ := exists_forms_idealOfVars_le_radical δ I hI hI' hdim.le
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle (idealOfVars_fg σ k)
  have hgen : ∀ d, max N e ≤ d → ∀ p : MvPolynomial σ k, p.IsHomogeneous d →
      ∃ G : Fin δ → MvPolynomial σ k,
        (∀ i, (G i).IsHomogeneous (d - e)) ∧ p - ∑ i, F i * G i ∈ I := fun d hd p hp =>
    exists_forms_sub_sum_mem hI hF hN (le_of_max_le_left hd) (le_of_max_le_right hd) hp
  have hfin : (aeval (fun i => Ideal.Quotient.mk I (F i)) :
      MvPolynomial (Fin δ) k →ₐ[k] MvPolynomial σ k ⧸ I).Finite := by
    refine finite_aeval_of_forms_eq_sum (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ_surjective k I)
      _ he (le_max_right N e) fun d hd p hp => ?_
    obtain ⟨G, hG, hs⟩ := hgen d hd p hp
    refine ⟨G, hG, ?_⟩
    have := Ideal.Quotient.eq.mpr hs
    simpa using this
  exact ⟨e, max N e, F, he, le_max_right N e, hF,
    injective_of_finite_of_ringKrullDim_eq _ hfin hdim, hgen, hfin⟩
end GlobalTheory
