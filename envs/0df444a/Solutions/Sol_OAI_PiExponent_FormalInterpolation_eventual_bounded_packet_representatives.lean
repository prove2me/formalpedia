-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eventual_bounded_packet_representatives
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T09:41:56.778015+00:00
-- url     : https://prove2.me/submissions/e870c5c3-098d-4b1a-b748-c1d0f663c985
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_bounded_packet_representatives_surjective

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

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
    ∃ N : Nat, ∀ n : Nat, N ≤ n → ∀ P : MvPolynomial (Fin (d.m + 1)) Complex,
      ∃ Q : WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real)),
        truncatedPolynomialPacket d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
          (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T P =
        truncatedPolynomialPacket d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
          (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T Q.val := by
  obtain ⟨N, hN⟩ := eventual_bounded_packet_representatives_surjective
    nu hnu d R T e hR he hT hscale
  refine ⟨N, ?_⟩
  intro n hn P
  obtain ⟨Q, hQ⟩ := hN n hn
    (truncatedPolynomialPacket d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T P)
  exact ⟨Q, hQ.symm⟩
