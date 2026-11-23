-- Prove2me | solution 2 for GrothendieckLB.Supplement.cq_tail_weighted_square_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T19:08:22.938585+00:00
-- url     : https://prove2.me/submissions/c9f20014-d8ea-4d77-b7a7-673be11ed966
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_cq_boundary_trace_fourier_coefficients
import Theorems.Thm_GrothendieckLB_Supplement_cq_boundary_trace_mean_square
import Theorems.Thm_GrothendieckLB_Supplement_cq_boundary_energy_quadrature
import Mathlib.Analysis.Real.Pi.Bounds

open MeasureTheory GrothendieckLB GrothendieckLB.Supplement

private theorem odd_mode_bessel (f : ℝ → ℂ) (b : ℕ → ℝ)
    (hab : (0:ℝ) < 2*Real.pi) (h2 : MemLp f 2 (volume.restrict (Set.Ioc 0 (2*Real.pi))))
    (hw : ∀ m : ℕ, fourierCoeffOn hab f (m:ℤ) = (m:ℂ)^3 * (b m : ℂ)) (n : ℕ) :
    (∑ j ∈ Finset.range n, ((251:ℝ)+2*((j:ℝ)+1))^6 * (b (2*j+253))^2) ≤
      (2*Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2*Real.pi, ‖f θ‖^2 := by
  let e : ℕ ↪ ℤ := ⟨fun j => ((2*j+253:ℕ):ℤ), fun i j h => by dsimp at h; omega⟩
  have P := hasSum_sq_fourierCoeffOn hab h2
  have B := P.summable.sum_le_tsum ((Finset.range n).map e)
    (fun i _ => sq_nonneg ‖fourierCoeffOn hab f i‖)
  rw [P.tsum_eq,sub_zero,smul_eq_mul,Finset.sum_map] at B
  apply le_trans ?_ B
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro j _
  change _ = ‖fourierCoeffOn hab f ((2*j+253:ℕ):ℤ)‖^2
  rw [hw, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]
  push_cast
  ring

theorem solution :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    ∀ n : ℕ, (∑ j ∈ Finset.range n,
      ((251 : ℝ) + 2 * ((j : ℝ) + 1)) ^ 6 *
        (taylorCoeff (2 * j + 253) H) ^ 2) ≤ (14.443 : ℝ) ^ 2 := by
  obtain ⟨hm,hf⟩ := cq_boundary_trace_fourier_coefficients
  dsimp only
  intro n
  refine (odd_mode_bessel _ _ (by positivity) hm hf n).trans (cq_boundary_trace_mean_square.trans ?_)
  calc
    _ ≤ Real.pi^2 / 6 * 126.80385221 :=
      mul_le_mul_of_nonneg_left cq_boundary_energy_quadrature (by positivity)
    _ ≤ 14.443^2 := by
      have hp := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d4.le 2
      linarith only [hp]
