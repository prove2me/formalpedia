-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:01:26.990462+00:00
-- url     : https://prove2.me/submissions/c9fe9d1d-f3e6-4139-9eb6-7642fd23cf9b

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Theorems.Thm_Kyprianou_Ch01_stableGammaIntegralByParts
import Theorems.Thm_Kyprianou_Ch01_stableGammaKernelIntegral
import Theorems.Thm_Kyprianou_Ch01_stableGammaNegativeRecurrence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Real
set_option autoImplicit false

/-- The stable gamma exponent follows from improper integration by parts,
    the positive Gamma Laplace kernel and the gamma recurrence. -/
theorem solution
    (alpha u : ℝ)
    (hα0 : 0 < alpha) (hα1 : alpha < 1)
    (hu : 0 < u) :
    IntegrableOn
      (fun x : ℝ =>
        (Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1))
      (Set.Ioi (0 : ℝ)) ∧
      (∫ x in Set.Ioi (0 : ℝ),
        (Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1) ∂volume) =
          Real.Gamma (-alpha) * u ^ alpha := by
  obtain ⟨hint, hIbP⟩ :=
    Kyprianou.Ch01.stableGammaIntegralByParts alpha u hα0 hα1 hu
  have hkernel :=
    Kyprianou.Ch01.stableGammaKernelIntegral alpha u hα0 hα1 hu
  have hgamma :=
    Kyprianou.Ch01.stableGammaNegativeRecurrence alpha hα0 hα1
  have hpow : (1 / u) ^ (1 - alpha) = u ^ (alpha - 1) := by
    rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  have hscale : u * (1 / u) ^ (1 - alpha) = u ^ alpha := by
    calc
      u * (1 / u) ^ (1 - alpha) = u ^ (1 : ℝ) * u ^ (alpha - 1) := by
        rw [Real.rpow_one, hpow]
      _ = u ^ (1 + (alpha - 1)) := (Real.rpow_add hu 1 (alpha - 1)).symm
      _ = u ^ alpha := by congr 1; ring
  refine ⟨hint, ?_⟩
  rw [hIbP, hkernel]
  calc
    -(u / alpha) * ((1 / u) ^ (1 - alpha) * Real.Gamma (1 - alpha)) =
      (-(Real.Gamma (1 - alpha)) / alpha) *
        (u * (1 / u) ^ (1 - alpha)) := by ring
    _ = Real.Gamma (-alpha) * u ^ alpha := by rw [← hgamma, hscale]
