-- Prove2me | solution 1 for MatousekLP.InteriorPoint.barrier_superlevel_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T21:22:10.455622+00:00
-- url     : https://prove2.me/submissions/c2d8d65f-2a6d-404e-b6df-01567b3badae

import Mathlib
import Definitions.Def_MatousekLP_InteriorPoint_CentralPath

open MatousekLP.InteriorPoint Matrix in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hrank : A.rank = m) (xt : Fin n → ℝ) (hxt : IsPrimalInterior A b xt)
    (yt : Fin m → ℝ) (hyt : IsDualInterior A c yt) (μ : ℝ) (hμ : 0 < μ) :
    Bornology.IsBounded
      {x : Fin n → ℝ | IsPrimalInterior A b x ∧ barrier c μ xt ≤ barrier c μ x} := by
  classical
  set s : Fin n → ℝ := Aᵀ *ᵥ yt - c with hs_def
  have hs : ∀ j, 0 < s j := hyt
  set C : Fin n → ℝ := fun j => μ * Real.log (2 * μ / s j) - μ with hC
  set M : ℝ := yt ⬝ᵥ b + ∑ j, C j - barrier c μ xt with hM
  refine (Metric.isBounded_Icc (0 : Fin n → ℝ) (fun j => 2 * M / s j)).subset ?_
  rintro x ⟨⟨hAx, hxpos⟩, hbar⟩
  have hc : c = Aᵀ *ᵥ yt - s := by rw [hs_def, sub_sub_cancel]
  have hcx : c ⬝ᵥ x = yt ⬝ᵥ b - s ⬝ᵥ x := by
    rw [hc, sub_dotProduct, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hAx]
  have hlog : ∀ j, μ * Real.log (x j) ≤ s j * x j / 2 + C j := by
    intro j
    have hsj := hs j
    have hxj := hxpos j
    have h1 : Real.log (x j) = Real.log (s j * x j / (2 * μ)) + Real.log (2 * μ / s j) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    have h2 := Real.log_le_sub_one_of_pos
      (show 0 < s j * x j / (2 * μ) by positivity)
    have h3 := mul_le_mul_of_nonneg_left h2 hμ.le
    have h4 : μ * (s j * x j / (2 * μ) - 1) = s j * x j / 2 - μ := by
      field_simp
    rw [h1, mul_add]
    simp only [hC]
    linarith
  have hsum : ∑ j, s j * x j / 2 ≤ M := by
    have hb : barrier c μ xt ≤ c ⬝ᵥ x + μ * ∑ j, Real.log (x j) := hbar
    rw [Finset.mul_sum] at hb
    have h5 := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hlog j)
    rw [Finset.sum_add_distrib] at h5
    have hsx : s ⬝ᵥ x = ∑ j, s j * x j := rfl
    have h6 : ∑ j, s j * x j / 2 = (∑ j, s j * x j) / 2 := by rw [Finset.sum_div]
    rw [hM]
    linarith
  refine ⟨fun j => (hxpos j).le, fun k => ?_⟩
  have hk : s k * x k / 2 ≤ M :=
    le_trans (Finset.single_le_sum (f := fun j => s j * x j / 2)
      (fun j _ => by have := hs j; have := hxpos j; positivity) (Finset.mem_univ k)) hsum
  show x k ≤ 2 * M / s k
  rw [le_div_iff₀ (hs k)]
  linarith
