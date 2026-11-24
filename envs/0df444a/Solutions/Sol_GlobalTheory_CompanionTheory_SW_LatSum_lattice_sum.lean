-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatSum.lattice_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:08:19.271795+00:00
-- url     : https://prove2.me/submissions/868ddb34-38a0-4b11-9169-5c733a33c8c9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EisensteinLatticeSumBound
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatSum_sum_int
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatSum_norm_lower
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatSum_finite_small
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatSum_sum_le_of_fibres
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatSum_fibre_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatSum
namespace GlobalTheory.CompanionTheory.SW.LatSum
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) →
    ∀ M : ℕ, 2 ≤ M → ∀ t : ℝ, 0 < t → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, t ≤ (τ w).im) →
      Summable (fun r : 𝓞 F => (∏ w, ‖τ w + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹) ∧
      ∑' r : 𝓞 F, (∏ w, ‖τ w + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹ ≤ C * ∏ w, (τ w).im * ((τ w).im ^ M)⁻¹ := by
  intro F _ _ _ ρ hρ M hM t ht
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 2 := ⟨M - 2, by omega⟩
  have hfin := finite_small F ρ hρ
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (2 + 1 / t)⁻¹ := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  refine ⟨(hfin.toFinset.card : ℝ) * ((c ^ (m + 2))⁻¹ * (2 * (1 + 1 / t))) ^
    Fintype.card (InfinitePlace F), fun τ hτ => ?_⟩
  have hy0 : ∀ w, 0 < (τ w).im := fun w => ht.trans_le (hτ w)
  have hint := fun w => sum_int ht (hτ w) m
  have hmain := sum_le_of_fibres
    (fun r : 𝓞 F => (∏ w, ‖τ w + (ρ w (r : F) : ℝ)‖ ^ (m + 2))⁻¹)
    (fun r w => ⌊(τ w).re + ρ w (r : F)⌋)
    (fun w k => (c ^ (m + 2))⁻¹ * ((|(k : ℝ)| + (τ w).im) ^ (m + 2))⁻¹)
    hfin.toFinset.card
    (fun r => by positivity)
    (fun w k => by have := hy0 w; positivity)
    (fun w => (hint w).1.mul_left _)
    (fun r => by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_
      have h1 := norm_lower ht (τ w) (hτ w) (ρ w (r : F))
      rw [← hc] at h1
      have hpos : 0 < c * (|((⌊(τ w).re + ρ w (r : F)⌋ : ℤ) : ℝ)| + (τ w).im) := by
        have := hy0 w
        positivity
      rw [← mul_inv, ← mul_pow]
      exact inv_anti₀ (pow_pos hpos _) (pow_le_pow_left₀ hpos.le h1 _))
    (fun T n => by
      classical
      exact fibre_card F ρ hfin.toFinset (fun α hα => hfin.mem_toFinset.2 hα)
        (fun w => (τ w).re) T n)
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  have hK : (0 : ℝ) ≤ hfin.toFinset.card := Nat.cast_nonneg _
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hK
  have hconst : ((c ^ (m + 2))⁻¹ * (2 * (1 + 1 / t))) ^ Fintype.card (InfinitePlace F)
      = ∏ _w : InfinitePlace F, ((c ^ (m + 2))⁻¹ * (2 * (1 + 1 / t))) := by
    rw [Finset.prod_const, Finset.card_univ]
  rw [hconst, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun w _ => ?_) fun w _ => ?_
  · exact tsum_nonneg fun k => by have := hy0 w; positivity
  · rw [tsum_mul_left, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (hint w).2
end GlobalTheory.CompanionTheory.SW.LatSum
