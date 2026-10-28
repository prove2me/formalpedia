-- Prove2me | solution 3 for OAI.PiExponent.FormalInterpolation.eventual_logarithmic_ideal_bounded_representatives
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T14:39:46.683557+00:00
-- url     : https://prove2.me/submissions/4726e274-2e1e-453e-81d0-93f4a727f645
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_bounded_packet_representatives
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_equal_truncated_packets_implies_ideal_power

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
        P - Q.val ∈ (logarithmicCentersIdeal
          (fun j : Fin d.K => fun i => (j.val : Complex) *
            MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
          T e) ^ n := by
  obtain ⟨N, hN⟩ :=
    OAI.PiExponent.FormalInterpolation.eventual_bounded_packet_representatives
      nu hnu d R T e hR he hT hscale
  refine ⟨N, ?_⟩
  intro n hn P
  obtain ⟨Q, hpacket⟩ := hN n hn P
  refine ⟨Q, ?_⟩
  exact OAI.PiExponent.FormalInterpolation.equal_truncated_packets_implies_ideal_power
    nu d R T e hR he hT hscale n P Q.val hpacket