-- Prove2me | solution 1 for LewisTorczon.BoundPS.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:37:09.206736+00:00
-- url     : https://prove2.me/submissions/81e77b41-7c0d-4de9-8f84-1ae9bfb287a5

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

theorem aux_l23_Δ_pos {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m)
    (hR : IsGPSRun P lo hi f R) : ∀ k, 0 < R.Δ k := by
  have hτ : (0 : ℝ) < (P.τ : ℝ) := by
    have : (0 : ℚ) < P.τ := lt_trans zero_lt_one P.one_lt_τ
    exact_mod_cast this
  intro k
  induction k with
  | zero => exact hR.Δ_zero_pos
  | succ k ih =>
    by_cases h : f (R.x k + R.s k) < f (R.x k)
    · obtain ⟨w, -, hw⟩ := hR.Δ_succ_success k h
      rw [hw]
      exact mul_pos (zpow_pos hτ w) ih
    · rw [hR.Δ_succ_failure k h]
      exact mul_pos (zpow_pos hτ _) ih

theorem aux_l23_norm_step {n : ℕ} (P : GPSParams n) (Δ : ℝ) (hΔ : 0 ≤ Δ) (c : Fin n → ℤ) :
    ‖stepOf P Δ c‖ ≤ Δ * (‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P.B‖ * ‖intVec c‖) := by
  have h1 : stepOf P Δ c = Δ • Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P.B (intVec c) := by
    simp [stepOf, intVec]
  rw [h1, norm_smul, Real.norm_of_nonneg hΔ]
  exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hΔ

end LewisTorczon.BoundPS

open LewisTorczon.BoundPS

theorem solution {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m)
    (hR : IsGPSRun P lo hi f R) (hbdd : BoundedCols R) :
    ∃ ψ : ℝ, 0 < ψ ∧ ∀ k, ∀ c ∈ cols R k, ψ * ‖stepOf P (R.Δ k) c‖ ≤ R.Δ k := by
  obtain ⟨C, hC, hcols⟩ := hbdd
  set K := ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P.B‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  have hD : 0 < K * C + 1 := by positivity
  refine ⟨1 / (K * C + 1), by positivity, ?_⟩
  intro k c hc
  have hΔ := aux_l23_Δ_pos P lo hi f R hR k
  have h1 := aux_l23_norm_step P (R.Δ k) hΔ.le c
  have h2 : ‖stepOf P (R.Δ k) c‖ ≤ R.Δ k * (K * C + 1) := by
    calc ‖stepOf P (R.Δ k) c‖ ≤ R.Δ k * (K * ‖intVec c‖) := h1
      _ ≤ R.Δ k * (K * C + 1) := by
        apply mul_le_mul_of_nonneg_left _ hΔ.le
        have := mul_le_mul_of_nonneg_left (hcols k c hc).le hK0
        linarith
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hD]
  exact h2
