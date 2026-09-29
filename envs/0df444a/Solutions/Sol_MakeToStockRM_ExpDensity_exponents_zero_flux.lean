-- Prove2me | solution 1 for MakeToStockRM.ExpDensity.exponents_zero_flux
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:41:28.674064+00:00
-- url     : https://prove2.me/submissions/344d5ef0-ba04-4939-97b6-7bd09565e6b6

import Mathlib
import Definitions.Def_MakeToStockRM_ExpDensity_generator
import Definitions.Def_MakeToStockRM_ExpDensity_covMatrix
import Definitions.Def_MakeToStockRM_ExpDensity_expDensity

namespace MakeToStockRM.ExpDensity

open Matrix

theorem aux_ezf_hasFDeriv (θ σ δ ϱ : ℝ) (z : ℝ × ℝ) :
    HasFDerivAt (expDensity θ σ δ ϱ)
      (Real.exp (mx θ σ ϱ * z.1 + my θ σ δ ϱ * z.2) •
        (mx θ σ ϱ • ContinuousLinearMap.fst ℝ ℝ ℝ + my θ σ δ ϱ • ContinuousLinearMap.snd ℝ ℝ ℝ)) z := by
  have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).const_mul (mx θ σ ϱ)
  have h2 := (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).const_mul (my θ σ δ ϱ)
  exact (h1.add h2).exp

theorem aux_ezf_px (θ σ δ ϱ : ℝ) (z : ℝ × ℝ) :
    partialX (expDensity θ σ δ ϱ) z = mx θ σ ϱ * expDensity θ σ δ ϱ z := by
  unfold partialX
  rw [(aux_ezf_hasFDeriv θ σ δ ϱ z).fderiv]
  simp [expDensity]
  ring

theorem aux_ezf_py (θ σ δ ϱ : ℝ) (z : ℝ × ℝ) :
    partialY (expDensity θ σ δ ϱ) z = my θ σ δ ϱ * expDensity θ σ δ ϱ z := by
  unfold partialY
  rw [(aux_ezf_hasFDeriv θ σ δ ϱ z).fderiv]
  simp [expDensity]
  ring

end MakeToStockRM.ExpDensity

open MakeToStockRM.ExpDensity
open Matrix

theorem solution (θ σ δ ϱ : ℝ) (hσ : 0 < σ) (hδ : 0 < δ) (hϱ : |ϱ| < 1) :
    ∀ z : ℝ × ℝ,
      (1 / 2 : ℝ) • (covMatrix σ δ ϱ *ᵥ
          ![partialX (expDensity θ σ δ ϱ) z, partialY (expDensity θ σ δ ϱ) z])
        = ![θ * expDensity θ σ δ ϱ z, 0] := by
  intro z
  have hr : 1 - ϱ ^ 2 ≠ 0 := by
    have := abs_lt.mp hϱ
    nlinarith
  have hσ' : σ ≠ 0 := hσ.ne'
  have hδ' : δ ≠ 0 := hδ.ne'
  rw [aux_ezf_px, aux_ezf_py]
  ext i
  fin_cases i
  · simp [covMatrix, mx, my]
    field_simp
    ring
  · simp [covMatrix, mx, my]
    field_simp
    ring
