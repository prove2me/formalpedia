-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eventual_weighted_representatives_of_scale
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T17:12:00.838983+00:00
-- url     : https://prove2.me/submissions/ded444c5-3345-46c5-a00b-bc06947f536b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_scaled_packet_right_inverse
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_power_of_packet_agreement
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals

open Filter Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    (nu : Real) (hnu : 2 < nu) (d : FixedData nu)
    (R : Rat) (T : Fin d.m → Nat) (e : Fin (d.m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (hscale : ∀ i, (R : Real) = (e i : Real) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i) :
    ∀ᶠ n : Nat in atTop,
      ∀ P : MvPolynomial (Fin (d.m + 1)) Complex,
        ∃ Q : FormalInterpolation.WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d))
          ((n : Real) * (R : Real)),
          P - Q.val ∈ FormalInterpolation.logarithmicCentersIdeal
            (fun j : Fin d.K => fun i => (j.val : Complex) *
              MatrixArithmetic.rationalCenters (finiteNumerators d)
                (finiteDenominators d) i) T e ^ n := by
  obtain ⟨N, hN⟩ := FormalInterpolation.eventual_scaled_packet_right_inverse
    nu hnu d R T e hR he hT hscale
  filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
  intro P
  obtain ⟨F, hF⟩ := hn
  let y : Row d ((n : Real) * (R : Real)) → Complex := fun ρ =>
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector ρ.2.val)
      (FormalInterpolation.formalJet (fun i => (ρ.1.val : Complex) *
        MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d) i) P)
  refine ⟨F y, ?_⟩
  apply FormalInterpolation.logarithmicCentersIdeal_power_of_packet_agreement
    nu hnu d R T e hR he hT hscale n P (F y)
  intro ρ
  exact congrFun (hF y) ρ
