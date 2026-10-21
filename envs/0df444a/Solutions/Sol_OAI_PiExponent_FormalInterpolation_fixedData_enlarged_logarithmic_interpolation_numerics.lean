-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fixedData_enlarged_logarithmic_interpolation_numerics
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:48:04.24111+00:00
-- url     : https://prove2.me/submissions/f5b26ba5-b06d-4a60-9249-26088dbe55eb

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_base_logarithmic_interpolation_numerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_interpolation_numerics_scaling_stability

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {nu : Real} (d : FixedData nu) :
    ∃ t : Real, 1 < t ∧
      ∃ w v : Fin (d.m + 1) → Rat,
        (∀ i, (w i : Real) = t *
          InterpolationMatrix.columnWeights d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) i) ∧
        (∀ i, (v i : Real) =
          InterpolationMatrix.rowWeights d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) i) ∧
        LogarithmicInterpolationNumerics d.m d.K w v d.sigma := by
  obtain ⟨w, v, hw, hv, hN⟩ :=
    fixedData_base_logarithmic_interpolation_numerics d
  obtain ⟨t, ht, w', v', hw', hv', hN'⟩ :=
    logarithmic_interpolation_numerics_scaling_stability
      d.m d.K d.sigma w v hN
  refine ⟨t, ht, w', v', ?_, ?_, hN'⟩
  · intro i
    rw [hw' i, hw i]
  · intro i
    rw [hv' i, hv i]