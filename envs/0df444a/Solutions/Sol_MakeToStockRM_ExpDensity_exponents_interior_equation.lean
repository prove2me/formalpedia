-- Prove2me | solution 1 for MakeToStockRM.ExpDensity.exponents_interior_equation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:04:37.725023+00:00
-- url     : https://prove2.me/submissions/4eedddc7-74bf-4faa-845e-0e3ea366ce8c

import Mathlib
import Definitions.Def_MakeToStockRM_ExpDensity_generator
import Definitions.Def_MakeToStockRM_ExpDensity_expDensity

namespace MakeToStockRM.ExpDensity

theorem aux_eie_hasFDeriv (a b c : ℝ) (z : ℝ × ℝ) :
    HasFDerivAt (fun w : ℝ × ℝ => c * Real.exp (a * w.1 + b * w.2))
      ((c * Real.exp (a * z.1 + b * z.2)) •
        (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)) z := by
  have h1 : HasFDerivAt (fun w : ℝ × ℝ => a * w.1 + b * w.2)
      (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) z := by
    have := ((hasFDerivAt_fst (𝕜 := ℝ) (p := z)).const_mul a).add
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := z)).const_mul b)
    exact this
  have h2 := (h1.exp).const_mul c
  rw [smul_smul] at h2
  exact h2

theorem aux_eie_partialX (a b c : ℝ) :
    partialX (fun w : ℝ × ℝ => c * Real.exp (a * w.1 + b * w.2))
      = fun w : ℝ × ℝ => (c * a) * Real.exp (a * w.1 + b * w.2) := by
  funext z
  unfold partialX
  rw [(aux_eie_hasFDeriv a b c z).fderiv]
  simp
  ring

theorem aux_eie_partialY (a b c : ℝ) :
    partialY (fun w : ℝ × ℝ => c * Real.exp (a * w.1 + b * w.2))
      = fun w : ℝ × ℝ => (c * b) * Real.exp (a * w.1 + b * w.2) := by
  funext z
  unfold partialY
  rw [(aux_eie_hasFDeriv a b c z).fderiv]
  simp
  ring

end MakeToStockRM.ExpDensity

open MakeToStockRM.ExpDensity

theorem solution (θ σ δ ϱ : ℝ) (hσ : 0 < σ) (hδ : 0 < δ) (hϱ : |ϱ| < 1) :
    ∀ z : ℝ × ℝ, adjointGenerator θ σ δ ϱ (expDensity θ σ δ ϱ) z = 0 := by
  intro z
  have hD : (1 - ϱ ^ 2) ≠ 0 := by
    have : ϱ ^ 2 < 1 := by
      have := abs_lt.mp hϱ
      nlinarith
    linarith
  have hf : expDensity θ σ δ ϱ
      = fun w : ℝ × ℝ => 1 * Real.exp (mx θ σ ϱ * w.1 + my θ σ δ ϱ * w.2) := by
    funext w; simp [expDensity]
  unfold adjointGenerator
  rw [hf, aux_eie_partialX, aux_eie_partialY, aux_eie_partialX, aux_eie_partialX,
    aux_eie_partialY]
  simp only
  unfold mx my
  have hσ' : σ ≠ 0 := hσ.ne'
  have hδ' : δ ≠ 0 := hδ.ne'
  field_simp
  ring
