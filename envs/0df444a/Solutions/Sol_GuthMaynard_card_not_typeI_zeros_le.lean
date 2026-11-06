-- Prove2me | solution 1 for GuthMaynard.card_not_typeI_zeros_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T21:34:57.048319+00:00
-- url     : https://prove2.me/submissions/1192634a-84cc-45d8-9488-ade17817c5d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_GuthMaynard_maynard_pratt_typeI_or_typeII
import Theorems.Thm_GuthMaynard_maynard_pratt_card_typeII_zeros_le

open scoped ENNReal

namespace GuthMaynard.CitedZeros

theorem mp_dev :
    ∃ A C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ,
      let D : ℕ → ℂ → ℂ := fun N s => ∑ n ∈ Finset.Ioc N (2 * N),
        ((∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ)),
            (ArithmeticFunction.moebius d : ℂ)) * (Real.exp (-(n : ℝ) / T ^ (1 / 2 : ℝ)) : ℂ)) *
          (n : ℂ) ^ (-s)
      (((∑' ρ : {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ ρ.im ∈ Set.Icc T (2 * T) ∧
          ¬ ∃ j : ℕ, (2 : ℝ) ^ j ∈ Set.Icc (T ^ (1 / 100 : ℝ)) (T ^ (1 / 2 : ℝ) * Real.log T ^ 2) ∧
            1 / (3 * Real.log T) ≤ ‖D (2 ^ j) ρ‖}, analyticOrderAt riemannZeta (ρ : ℂ)) : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (2 - 2 * σ) * Real.log T ^ A) := by
  obtain ⟨T₁, h23⟩ := GuthMaynard.maynard_pratt_typeI_or_typeII
  obtain ⟨A, C, T₂, h24⟩ := GuthMaynard.maynard_pratt_card_typeII_zeros_le
  refine ⟨A, C, max T₁ T₂, fun T hT σ => ?_⟩
  have h1 := h23 T (le_of_max_le_left hT)
  have h2 := h24 T (le_of_max_le_right hT) σ
  intro D
  simp only [] at h1 h2
  refine le_trans ?_ h2
  apply ENat.toENNReal_le.mpr
  refine Summable.tsum_le_tsum_of_inj (Set.inclusion ?_) (Set.inclusion_injective _)
    (fun _ _ => zero_le) (fun _ => le_rfl)
    ⟨_, hasSum_of_isLUB _ (isLUB_sSup _)⟩ ⟨_, hasSum_of_isLUB _ (isLUB_sSup _)⟩
  intro ρ hρ
  obtain ⟨h0, hs, hi, hn⟩ := hρ
  exact ⟨h0, hs, hi, (h1 ρ h0 hi).resolve_left hn⟩

end GuthMaynard.CitedZeros

open scoped ENNReal in
theorem solution :
    ∃ A C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ,
      let D : ℕ → ℂ → ℂ := fun N s => ∑ n ∈ Finset.Ioc N (2 * N),
        ((∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ)),
            (ArithmeticFunction.moebius d : ℂ)) * (Real.exp (-(n : ℝ) / T ^ (1 / 2 : ℝ)) : ℂ)) *
          (n : ℂ) ^ (-s)
      (((∑' ρ : {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ ρ.im ∈ Set.Icc T (2 * T) ∧
          ¬ ∃ j : ℕ, (2 : ℝ) ^ j ∈ Set.Icc (T ^ (1 / 100 : ℝ)) (T ^ (1 / 2 : ℝ) * Real.log T ^ 2) ∧
            1 / (3 * Real.log T) ≤ ‖D (2 ^ j) ρ‖}, analyticOrderAt riemannZeta (ρ : ℂ)) : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (2 - 2 * σ) * Real.log T ^ A) :=
  GuthMaynard.CitedZeros.mp_dev
