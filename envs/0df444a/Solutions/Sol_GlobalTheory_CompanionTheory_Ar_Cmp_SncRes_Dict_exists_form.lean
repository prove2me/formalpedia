-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.exists_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:21:43.154809+00:00
-- url     : https://prove2.me/submissions/f93cdfbe-2146-447b-be9a-e0191cbc7055

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturated
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_isMultiHomog_C
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_isMultiHomog_add
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_isMultiHomog_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_isMultiHomog_X
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dict_isMultiHomog_chartMonomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
theorem _root_.solution (p : (k : K) → ι k) (I : Ideal (MvPolynomial (Σ k, ι k) ℂ))
    (hI : ∀ k, (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ I) (g : MvPolynomial (Σ k, ι k) ℂ) :
    ∃ (d : K → ℕ) (H : MvPolynomial (Σ k, ι k) ℂ), IsMultiHomog H d ∧ H - g ∈ I := by
  classical
  have hM : ∀ e : K → ℕ, (∏ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ^ e k) - 1 ∈ I := by
    intro e
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_prod, sub_eq_zero]
    refine Finset.prod_eq_one fun k _ => ?_
    have : Ideal.Quotient.mk I (X ⟨k, p k⟩) = 1 := by
      have := Ideal.Quotient.eq_zero_iff_mem.2 (hI k)
      rwa [map_sub, map_one, sub_eq_zero] at this
    rw [map_pow, this, one_pow]
  induction g using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, isMultiHomog_C a, by simp⟩
  | add u v hu hv =>
    obtain ⟨d₁, H₁, h₁, m₁⟩ := hu
    obtain ⟨d₂, H₂, h₂, m₂⟩ := hv
    set M₁ := ∏ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ^ d₁ k with hM₁
    set M₂ := ∏ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ^ d₂ k with hM₂
    refine ⟨d₁ + d₂, H₁ * M₂ + H₂ * M₁, isMultiHomog_add
      (isMultiHomog_mul h₁ (isMultiHomog_chartMonomial p d₂))
      (add_comm d₂ d₁ ▸ isMultiHomog_mul h₂ (isMultiHomog_chartMonomial p d₁)), ?_⟩
    have e : H₁ * M₂ + H₂ * M₁ - (u + v) =
        M₂ * (H₁ - u) + u * (M₂ - 1) + M₁ * (H₂ - v) + v * (M₁ - 1) := by ring
    rw [e]
    exact I.add_mem (I.add_mem (I.add_mem (I.mul_mem_left _ m₁) (I.mul_mem_left _ (hM d₂)))
      (I.mul_mem_left _ m₂)) (I.mul_mem_left _ (hM d₁))
  | mul_X u s hu =>
    obtain ⟨d, H, h, m⟩ := hu
    refine ⟨d + Pi.single s.1 1, H * X s, isMultiHomog_mul h (isMultiHomog_X s), ?_⟩
    have e : H * X s - u * X s = X s * (H - u) := by ring
    rw [e]
    exact I.mul_mem_left _ m
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
