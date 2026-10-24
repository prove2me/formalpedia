-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.eventual_fixed_minor_arithmetic_lower_bound_fixed_height_core_scaled_denominator_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:58:40.723876+00:00
-- url     : https://prove2.me/submissions/91f20536-fdec-4b1e-b4bc-04e99f1401de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_scaled_denominator_log_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_nonzero_gaussian_integer_scaled_norm_bounds
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_row_count_pos

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    {nu : Real} (d : FixedData nu) (H : Real) (hH : 0 < H)
    (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    0 < (actualRowCount d H : Real) * H ∧
      ∃ D : Nat, 0 < D ∧
        ∃ a b : Int,
          (D : Complex) * (actualMinor d H selection).det =
              (a : Complex) + Complex.I * (b : Complex) ∧
            1 ≤ (D : Real) * ‖(actualMinor d H selection).det‖ ∧
            -(Real.log (D : Real)) ≤
              Real.log ‖(actualMinor d H selection).det‖ ∧
            Real.log (D : Real) ≤
              ((actualRowCount d H : Real) * H) *
                (1 - actualMean d H + d.arithmeticError) := by
  obtain ⟨D, hD, a, b, hscale, hlogD⟩ :=
    OAI.PiExponent.DeterminantContradiction.scaled_denominator_log_bound
      d H hH selection hdet
  have hnorm :=
    OAI.PiExponent.DeterminantContradiction.nonzero_gaussian_integer_scaled_norm_bounds
      hdet D hD a b hscale
  have hprod : 0 < (actualRowCount d H : Real) * H :=
    mul_pos (OAI.PiExponent.DeterminantContradiction.actual_row_count_pos d H hH) hH
  exact ⟨hprod, D, hD, a, b, hscale, hnorm.1, hnorm.2, hlogD⟩