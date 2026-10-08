-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eventual_weighted_representatives_mod_logarithmic_ideal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T06:30:56.638482+00:00
-- url     : https://prove2.me/submissions/e0f393b7-0568-4e51-b797-8f2b6a8391a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_representative_scale_exists
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_weighted_representatives_of_scale

open Filter Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    (nu : ℝ) (hnu : 2 < nu) (d : FixedData nu) :
    ∃ (R : ℚ) (T : Fin d.m → ℕ) (e : Fin (d.m + 1) → ℕ),
      0 < R ∧ (∀ i, 0 < e i) ∧
      (∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
        (T i : ℝ) * InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) 0) ∧
      (∀ i, (R : ℝ) = (e i : ℝ) *
        InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) i) ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
          ∃ Q : FormalInterpolation.WeightedPolynomial d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * (R : ℝ)),
            P - Q.val ∈ FormalInterpolation.logarithmicCentersIdeal
              (fun j : Fin d.K => fun i => (j.val : ℂ) *
                MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
              T e ^ n := by
  obtain ⟨R, T, e, hR, he, hT, hscale⟩ :=
    FormalInterpolation.weighted_representative_scale_exists nu hnu d
  exact ⟨R, T, e, hR, he, hT, hscale,
    FormalInterpolation.eventual_weighted_representatives_of_scale
      nu hnu d R T e hR he hT hscale⟩
