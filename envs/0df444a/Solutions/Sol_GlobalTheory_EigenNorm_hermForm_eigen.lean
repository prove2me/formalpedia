-- Prove2me | solution 1 for GlobalTheory.EigenNorm.hermForm_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:42:38.612914+00:00
-- url     : https://prove2.me/submissions/74ad0d5f-e707-49ad-b906-bfc9fddeab1d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_add_left
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_add_right
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_smul_left
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_smul_right
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_sum_left
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_sum_right
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_conj
import Theorems.Thm_GlobalTheory_EigenNorm_eq_zero_of_sum_embedding_mul
import Theorems.Thm_GlobalTheory_EigenNorm_conj_eq_neg_of_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.EigenNorm
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
namespace GlobalTheory.EigenNorm
theorem _root_.solution :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian →
  ∀ (L : Type) [AddCommGroup L] [Module (𝓞 E) L] (h : L → L → E) (ρ : ℂ) (c : ℝ) (x : (E →+* ℂ) → L →+ (Fin g → ℂ)),
  ρ ^ 2 = -(H.d : ℂ) → (∀ a b e, h (a + b) e = h a e + h b e) → (∀ (s : 𝓞 E) a e, h (s • a) e = s * h a e) →
  (∀ a b, h b a = IsCMField.complexConj E (h a b)) →
  (∀ τ (s : 𝓞 E) a, x τ (s • a) = τ (s : E) • x τ a) → (∀ τ, τ (H.rt : E) ≠ ρ → x τ = 0) →
  (∀ a, hermForm Hm (∑ τ, x τ a) (∑ τ, x τ a) = c * ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = ρ), τ (h a a)) →
  ∀ τ τ' a b, τ (H.rt : E) = ρ → hermForm Hm (x τ a) (x τ' b) = open Classical in if τ' = τ then c * τ (h a b) else 0 := by
  intro E _ _ _ H g Hm hH L _ _ h ρ c x hρ hadd hsmul hsymm hx hx0 hq τ τ' a b hτ
  classical
  have hd : H.d ≠ 0 := H.d_prime.ne_zero
  have hρc := conj_eq_neg_of_sq hd hρ
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    apply hd
    have : (H.d : ℂ) = 0 := by simpa using hρ.symm
    exact_mod_cast this
  have hconj : ∀ (σ : E →+* ℂ) a b, σ (h b a) = starRingEnd ℂ (σ (h a b)) := fun σ a b => by
    rw [hsymm a b, IsCMField.complexEmbedding_complexConj]
  have haddr : ∀ (σ : E →+* ℂ) e a b, σ (h e (a + b)) = σ (h e a) + σ (h e b) := fun σ e a b => by
    rw [hconj σ (a + b) e, hconj σ a e, hconj σ b e, hadd, map_add, map_add]
  have hsmulr : ∀ (σ : E →+* ℂ) (s : 𝓞 E) e a, σ (h e (s • a)) = starRingEnd ℂ (σ s) * σ (h e a) :=
    fun σ s e a => by rw [hconj σ (s • a) e, hconj σ a e, hsmul, map_mul, map_mul]
  set Ψ := Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = ρ) with hΨ
  let D : L → L → ℂ := fun a b =>
    hermForm Hm (∑ τ, x τ a) (∑ τ, x τ b) - c * ∑ τ ∈ Ψ, τ (h a b)
  have hD0 : ∀ a, D a a = 0 := fun a => sub_eq_zero.2 (hq a)
  have hDc : ∀ a b, D b a = starRingEnd ℂ (D a b) := fun a b => by
    simp only [D, map_sub, map_mul, map_sum, Complex.conj_ofReal, ← hconj]
    rw [hermForm_conj Hm hH]
  have hDl : ∀ a b e, D (a + b) e = D a e + D b e := fun a b e => by
    simp only [D, map_add, hadd, Finset.sum_add_distrib, hermForm_add_left]; ring
  have hDr : ∀ e a b, D e (a + b) = D e a + D e b := fun e a b => by
    simp only [D, map_add, haddr, Finset.sum_add_distrib, hermForm_add_right]; ring
  have hDpol : ∀ a b, D a b + starRingEnd ℂ (D a b) = 0 := fun a b => by
    have := hD0 (a + b)
    rw [hDl, hDr, hDr, hD0, hD0, hDc a b] at this
    linear_combination this
  have hDrt : ∀ a b, D (H.rt • a) b = ρ * D a b := fun a b => by
    have h1 : ∑ τ, x τ (H.rt • a) = ρ • ∑ τ, x τ a := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      by_cases hσ : σ (H.rt : E) = ρ
      · rw [hx, hσ]
      · simp [hx0 σ hσ]
    have h2 : ∑ τ ∈ Ψ, τ (h (H.rt • a) b) = ρ * ∑ τ ∈ Ψ, τ (h a b) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ hσ => ?_
      rw [hsmul, map_mul, (Finset.mem_filter.1 hσ).2]
    simp only [D]
    rw [h1, h2, hermForm_smul_left]; ring
  have hD : ∀ a b, D a b = 0 := fun a b => by
    have h1 := hDpol a b
    have h2 := hDpol (H.rt • a) b
    rw [hDrt, map_mul, hρc] at h2
    have h3 : ρ * (2 * D a b) = 0 := by linear_combination h2 + ρ * h1
    simpa [hρ0] using h3
  have hstep : ∀ b, hermForm Hm (x τ a) (∑ σ, x σ b) = c * τ (h a b) := fun b => by
    have := eq_zero_of_sum_embedding_mul
      (fun σ : E →+* ℂ => hermForm Hm (x σ a) (∑ σ, x σ b) -
        if σ (H.rt : E) = ρ then (c : ℂ) * σ (h a b) else 0) (fun s => ?_) τ
    · simpa [hτ, sub_eq_zero] using this
    have h1 := hD (s • a) b
    simp only [D, hΨ] at h1
    rw [hermForm_sum_left, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib] at h1
    refine Eq.trans (Finset.sum_congr rfl fun σ _ => ?_) h1
    rw [hx, hermForm_smul_left, hsmul, map_mul]
    split_ifs <;> ring
  have := eq_zero_of_sum_embedding_mul
    (fun σ : E →+* ℂ => starRingEnd ℂ (hermForm Hm (x τ a) (x σ b) -
      if σ = τ then (c : ℂ) * τ (h a b) else 0)) (fun s => ?_) τ'
  · rw [map_eq_zero, sub_eq_zero] at this
    convert this
  have h1 := hstep (s • b)
  rw [hermForm_sum_right, hsmulr] at h1
  simp only [hx, hermForm_smul_right] at h1
  have h2 : ∑ σ : E →+* ℂ, starRingEnd ℂ (σ (s : E)) * (hermForm Hm (x τ a) (x σ b) -
      if σ = τ then (c : ℂ) * τ (h a b) else 0) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, h1, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have h3 := congrArg (starRingEnd ℂ) h2
  simpa only [map_sum, map_mul, Complex.conj_conj, map_zero] using h3
end GlobalTheory.EigenNorm
