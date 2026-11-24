-- Prove2me | solution 1 for GlobalTheory.UnRep.normOne_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:17:58.248828+00:00
-- url     : https://prove2.me/submissions/d62df737-1c04-4bb1-b356-edf6b2a0ab32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationEqOneOfNormOneOfNotMoved
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsDenominatorPrimesPrescribed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneApproximationAtLevelPrimes
import Theorems.Thm_GlobalTheory_UnRep_NormOne_exists_split
import Theorems.Thm_GlobalTheory_UnRep_NormOne_exists_nat_multiple
import Theorems.Thm_GlobalTheory_UnRep_NormOne_one_add_ne_zero
import Theorems.Thm_GlobalTheory_UnRep_NormOne_exists_coprime_multiple
import Theorems.Thm_GlobalTheory_UnRep_NormOne_val_le_of_unit
import Theorems.Thm_GlobalTheory_UnRep_NormOne_val_le_of_cong
import Theorems.Thm_GlobalTheory_UnRep_NormOne_exists_conj
import Theorems.Thm_GlobalTheory_UnRep_NormOne_hilbert90_matrix_subalgebra_norm_one
import Theorems.Thm_GlobalTheory_UnRep_exists_denominator_primes_prescribed
import Theorems.Thm_GlobalTheory_UnRep_valuation_eq_one_of_norm_one_of_not_moved


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory.UnRep.NormOne
namespace GlobalTheory.UnRep
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), (∀ x, c (c x) = x) → c ≠ 1 → ∀ (u : E) (N D : ℕ), u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ (∃ t : ℕ, t.Coprime N ∧ ∃ b : 𝓞 E, (t : E) * (u' / u - 1) = (D : E) * (b : E)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ (∃ b : 𝓞 E, (s : E) * (u' - 1) = (D : E) * (b : E)) ∧ ∃ b : 𝓞 E, (s : E) * (u'⁻¹ - 1) = (D : E) * (b : E) := by
  intro F E _ _ _ _ _ c hc hc1 u N D hu hN hD
  by_cases hN1 : N = 1
  · subst hN1
    refine ⟨1, by simp, ⟨0, by simp, 0, by simp⟩, 1, ⟨one_ne_zero, fun P hP h => Or.inr (by simpa using h)⟩,
      ⟨0, by simp⟩, 0, by simp⟩
  obtain ⟨α, hα, huα⟩ := hilbert90_matrix_subalgebra_norm_one c hc hc1 u hu
  obtain ⟨β, hβc⟩ := exists_conj c α
  have hαE : (α : E) ≠ 0 := by exact_mod_cast hα
  have hβE : (β : E) ≠ 0 := by rw [hβc]; simpa using hαE
  have hβ : β ≠ 0 := by intro h; apply hβE; rw [h]; rfl
  obtain ⟨n₁, hn₁, γ₁, hγ₁⟩ := exists_nat_multiple α hα
  obtain ⟨n₂, hn₂, γ₂, hγ₂⟩ := exists_nat_multiple β hβ
  obtain ⟨D₁, D₂, k, hM, h1, h2⟩ := exists_split N (D * (n₁ * n₂)) (by positivity)
  have hco : D₂.Coprime (D₁ * N) :=
    Nat.Coprime.mul_right (Nat.Coprime.coprime_dvd_right h1 (Nat.Coprime.pow_right k h2)) h2
  obtain ⟨p, q, hpq⟩ := Nat.isCoprime_iff_coprime.mpr hco
  have hpq' : (p : 𝓞 E) * D₂ + q * (D₁ * N) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hpq
  have hM' : (D : 𝓞 E) * (α * γ₁ * (β * γ₂)) = D₁ * D₂ := by
    rw [← hγ₁, ← hγ₂]; exact_mod_cast hM
  set b : 𝓞 E := q * (D₁ * N) with hb
  set α' : 𝓞 E := p * D₂ * α + b with hα'
  set β' : 𝓞 E := p * D₂ * β + b with hβ'
  have hcα' : c α' = β' := by
    simp only [hα', hβ', hb, RingOfIntegers.coe_eq_algebraMap, map_mul, map_add, map_natCast, map_intCast] at hβc ⊢
    rw [hβc]
  have hcβ' : c β' = α' := by rw [← hcα', hc]
  set z : 𝓞 E := -2 * q * D₁ + q * D₁ * b + p * q * (D * α * γ₁ * γ₂) with hz
  have hw := one_add_ne_zero N hN1 z
  obtain ⟨t, ht, γ, hγ⟩ := exists_coprime_multiple N hN z hw
  have e1 : p * D₂ * β' = β * (1 + N * z) := by
    rw [hβ', hz, hb]
    linear_combination (β * (p * D₂ + 1 - q * (D₁ * N))) * hpq' - (p * q * N : 𝓞 E) * hM'
  have hβ'0 : β' ≠ 0 := by
    intro h
    rw [h, mul_zero] at e1
    exact mul_ne_zero hβ hw e1.symm
  have hβ'E : (β' : E) ≠ 0 := by exact_mod_cast hβ'0
  have hα'E : (α' : E) ≠ 0 := by rw [← hcβ']; simpa using hβ'E
  have hu' : (α' : E) / β' * c ((α' : E) / β') = 1 := by
    rw [map_div₀, hcα', hcβ']; field_simp
  have hDE : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
  refine ⟨(α' : E) / β', hu', ⟨t, ht, γ * p * q * N * γ₁ * γ₂ * (β - α), ?_⟩, ?_⟩
  · have hu2 : u = (α : E) / β := by rw [eq_div_iff hβE, hβc, huα]
    have e2 : (t : 𝓞 E) * (α' * β - β' * α) = D * (γ * p * q * N * γ₁ * γ₂ * (β - α)) * (β' * α) := by
      apply mul_left_cancel₀ hβ
      have e3 : α' * β - β' * α = b * (β - α) := by rw [hα', hβ']; ring
      rw [e3, hγ, hb]
      linear_combination (-(γ * q * D₁ * N * (β - α))) * e1 - (γ * p * q * N * (β - α) * β') * hM'
    generalize γ * p * q * N * γ₁ * γ₂ * (β - α) = g at e2 ⊢
    have e4 := congrArg (algebraMap (𝓞 E) E) e2
    simp only [map_mul, map_sub, map_natCast] at e4
    rw [hu2]
    field_simp
    simp only [RingOfIntegers.coe_eq_algebraMap] at e4 ⊢
    linear_combination e4
  · have hM2 : D * (n₁ * n₂) = D₁ * D₂ := hM
    obtain ⟨s, hs0, hsP, hs⟩ := GlobalTheory.UnRep.exists_denominator_primes_prescribed E (fun P => Moved c P ∨ (N : 𝓞 E) ∈ P) Bool
      (fun i => if i then ((α' : E) / β' - 1) / D else (((α' : E) / β')⁻¹ - 1) / D) (by
        intro i P hQ
        rw [not_or] at hQ
        have hv := GlobalTheory.UnRep.valuation_eq_one_of_norm_one_of_not_moved F E c hc _ P hu' hQ.1
        by_cases hDP : (D : 𝓞 E) ∈ P.asIdeal
        · cases i
          · simp only [Bool.false_eq_true, if_false, inv_div]
            exact val_le_of_cong P N D D₁ D₂ k _ hD hM2 h1 hQ.2 hDP β α p b hpq'
          · simp only [if_true]
            exact val_le_of_cong P N D D₁ D₂ k _ hD hM2 h1 hQ.2 hDP α β p b hpq'
        · cases i
          · simp only [Bool.false_eq_true, if_false]
            exact val_le_of_unit P _ D hDP (by rw [map_inv₀, hv, inv_one])
          · simp only [if_true]
            exact val_le_of_unit P _ D hDP hv)
    obtain ⟨b₁, hb₁⟩ := hs true
    obtain ⟨b₂, hb₂⟩ := hs false
    simp only [if_true] at hb₁
    simp only [Bool.false_eq_true, if_false] at hb₂
    refine ⟨s, ⟨hs0, hsP⟩, ⟨b₁, ?_⟩, b₂, ?_⟩
    · rw [← hb₁, mul_left_comm, mul_div_cancel₀ _ hDE]
    · rw [← hb₂, mul_left_comm, mul_div_cancel₀ _ hDE]
end GlobalTheory.UnRep
