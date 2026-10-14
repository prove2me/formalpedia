-- Prove2me | solution 1 for MDOUnifiedCosmology.parameter_inversion
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:13:43.108109+00:00
-- url     : https://prove2.me/submissions/8bd2e257-3177-4718-8ffd-41102c323b0c

import Definitions.Def_MDOUnifiedCosmology_model
open MDOUnifiedCosmology Set

theorem solution (κ mpl H₀ ρb₀ φc m α : ℝ) (hmpl : 0 < mpl)
    (hκ : κ ^ 2 = 8 * Real.pi / mpl ^ 2) (hH₀ : H₀ ≠ 0) (hρb₀ : 0 < ρb₀) (hφc : 0 < φc) :
    φc = mpl * Real.sqrt (omegaDM κ φc (omegaB κ H₀ ρb₀) / (Real.pi * omegaB κ H₀ ρb₀)) ∧
    V2 m α φc = omegaLambda κ H₀ φc m α /
        (1 + omegaDM κ φc (omegaB κ H₀ ρb₀) / omegaB κ H₀ ρb₀) * critDensity κ H₀ := by
  have hk2 : 0 < κ^2 := by rw [hκ]; positivity
  have hk : κ ≠ 0 := by intro h; simp [h] at hk2
  have hcr : 0 < critDensity κ H₀ := by unfold critDensity; positivity
  have hb : 0 < omegaB κ H₀ ρb₀ := div_pos hρb₀ hcr
  have hC : couplingFactor κ φc ≠ 0 := ne_of_gt (by unfold couplingFactor; positivity)
  have he : omegaDM κ φc (omegaB κ H₀ ρb₀) / (Real.pi * omegaB κ H₀ ρb₀) = (φc / mpl)^2 := by
    unfold omegaDM
    rw [hκ]
    field_simp [hk] <;> ring
  constructor
  · rw [he, Real.sqrt_sq (le_of_lt (div_pos hφc hmpl))]
    field_simp [hk]
  · have hd : 1 + omegaDM κ φc (omegaB κ H₀ ρb₀) / omegaB κ H₀ ρb₀ = couplingFactor κ φc := by
      unfold omegaDM couplingFactor
      field_simp [hk]
    rw [hd]
    unfold omegaLambda lambdaEff
    field_simp [hk]



