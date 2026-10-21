-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_packet_surjective_of_matrix_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T05:31:38.43974+00:00
-- url     : https://prove2.me/submissions/8d0ea98c-1328-4b7a-af12-8b7d47f84f26

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_matrix_image_representative

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    (nu : Real) (d : FixedData nu)
    (R : Rat) (T : Fin d.m → Nat) (e : Fin (d.m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (hscale : ∀ i, (R : Real) = (e i : Real) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i)
    (n : Nat)
    (hmat : Function.Surjective
      (InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d))
        ((n : Real) * (R : Real))
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
        T).mulVecLin)
    (y : InterpolationMatrix.Row d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real)) → Complex) :
    ∃ Q : WeightedPolynomial d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real)),
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T Q.val = y := by
  obtain ⟨x, hx⟩ := hmat y
  obtain ⟨Q, hQ⟩ := OAI.PiExponent.FormalInterpolation.truncated_packet_matrix_image_representative
    d.K d.w0 d.v0 d.base.theta (MatrixArithmetic.logWeights (finiteDenominators d))
    ((n : Real) * (R : Real))
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T x
  refine ⟨Q, ?_⟩
  rw [hQ]
  exact hx
