-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fixedData_canonical_logarithmic_interpolation_numerics
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T12:37:21.055347+00:00
-- url     : https://prove2.me/submissions/6cb82a3c-7c78-4f30-8f07-fa081c9d7952

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_canonical_log_weights_positive
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_canonical_log_volume_bounds
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_canonical_log_separation
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_canonical_log_coordinate_ratio

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    let w : Fin (d.m + 1) -> Rat :=
      fun i => Fin.cases d.w0
        (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
    let v : Fin (d.m + 1) -> Rat :=
      fun i => Fin.cases d.v0
        (fun j =>
          (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
    (forall i, (w i : Real) =
      OAI.PiExponent.InterpolationMatrix.columnWeights d.w0
        (OAI.PiExponent.MatrixArithmetic.logWeights
          (OAI.PiExponent.DeterminantContradiction.finiteDenominators d)) i) /\
    (forall i, (v i : Real) =
      OAI.PiExponent.InterpolationMatrix.rowWeights d.v0 d.base.theta
        (OAI.PiExponent.MatrixArithmetic.logWeights
          (OAI.PiExponent.DeterminantContradiction.finiteDenominators d)) i) /\
    OAI.PiExponent.FormalInterpolation.LogarithmicInterpolationNumerics
      d.m d.K w v d.sigma := by
  let w : Fin (d.m + 1) -> Rat := fun i => Fin.cases d.w0
    (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
  let v : Fin (d.m + 1) -> Rat := fun i => Fin.cases d.v0
    (fun j => (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ ?_ i
    · simp [w, InterpolationMatrix.columnWeights]
    · intro j
      simp [w, InterpolationMatrix.columnWeights, MatrixArithmetic.logWeights,
        DeterminantContradiction.finiteDenominators]
  · intro i
    refine Fin.cases ?_ ?_ i
    · simp [v, InterpolationMatrix.rowWeights]
    · intro j
      simp [v, InterpolationMatrix.rowWeights, MatrixArithmetic.logWeights,
        DeterminantContradiction.finiteDenominators]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_weights_positive d).1
    · exact d.K_pos
    · exact d.sigma_pos
    · exact (OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_weights_positive d).2.1
    · exact (OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_weights_positive d).2.2
    · exact (OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_volume_bounds d).1
    · exact (OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_volume_bounds d).2
    · exact OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_separation d
    · exact OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_coordinate_ratio d