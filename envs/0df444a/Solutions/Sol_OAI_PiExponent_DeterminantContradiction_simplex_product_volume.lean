-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_product_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:24:15.040616+00:00
-- url     : https://prove2.me/submissions/375a2c79-4ecc-45e1-8c2d-152ff4c1a3a5

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_simplexRegion
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_scaling_by_cutoff
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_unit_volume_by_dimension

open scoped BigOperators

theorem solution (n : Nat) (T : Real) (hT : 0 < T) :
    MeasureTheory.volume {z : Real × (Fin n → Real) | 0 ≤ z.1 ∧ (∀ i, 0 ≤ z.2 i) ∧ z.1 + (∑ i, z.2 i) < T} =
      ENNReal.ofReal (T ^ (n + 1) / (Nat.factorial (n + 1) : Real)) := by
  change MeasureTheory.volume
      (OAI.PiExponent.DeterminantContradiction.simplexRegion n T) =
    ENNReal.ofReal (T ^ (n + 1) / (Nat.factorial (n + 1) : Real))
  have hscale := OAI.PiExponent.DeterminantContradiction.simplex_volume_scaling_by_cutoff n T hT
  have hone := OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_by_dimension n
  rw [hscale, hone]
  have hreal :
      T ^ (n + 1) / (Nat.factorial (n + 1) : Real) =
        T ^ (n + 1) * (1 / (Nat.factorial (n + 1) : Real)) := by
    ring
  rw [hreal]
  rw [mul_comm (ENNReal.ofReal (T ^ (n + 1)))
    (ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)))]
  rw [← ENNReal.ofReal_mul
    (by positivity : 0 ≤ (1 / (Nat.factorial (n + 1) : Real)))]
  congr 1
  ring