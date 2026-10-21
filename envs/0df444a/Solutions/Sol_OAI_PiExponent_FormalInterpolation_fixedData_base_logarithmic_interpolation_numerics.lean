-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fixedData_base_logarithmic_interpolation_numerics
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:53:09.041987+00:00
-- url     : https://prove2.me/submissions/a7e26fee-e310-4ad6-9c38-79e5b980834e

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_canonical_logarithmic_interpolation_numerics

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    exists w v : Fin (d.m + 1) -> Rat,
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
  let w : Fin (d.m + 1) -> Rat :=
    fun i => Fin.cases d.w0
      (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
  let v : Fin (d.m + 1) -> Rat :=
    fun i => Fin.cases d.v0
      (fun j =>
        (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
  obtain ⟨hw, hv, hnum⟩ :=
    OAI.PiExponent.FormalInterpolation.fixedData_canonical_logarithmic_interpolation_numerics d
  exact ⟨w, v, hw, hv, hnum⟩