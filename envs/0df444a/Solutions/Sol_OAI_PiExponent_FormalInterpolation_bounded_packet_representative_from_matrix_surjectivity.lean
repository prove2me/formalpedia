-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_packet_representative_from_matrix_surjectivity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T05:27:14.408217+00:00
-- url     : https://prove2.me/submissions/c4ea5394-58f8-410a-ae24-10b84e7f7a30
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_surjective_of_matrix_surjective

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
    (n : Nat) (P : MvPolynomial (Fin (d.m + 1)) Complex)
    (hmat : Function.Surjective
      (InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d))
        ((n : Real) * (R : Real))
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
        T).mulVecLin) :
    ∃ Q : WeightedPolynomial d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real)),
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T P =
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T Q.val := by
  obtain ⟨Q, hQ⟩ :=
    OAI.PiExponent.FormalInterpolation.truncated_packet_surjective_of_matrix_surjective
      nu d R T e hR he hT hscale n hmat
      (truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T P)
  exact ⟨Q, hQ.symm⟩
