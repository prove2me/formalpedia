-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eventual_scaled_packet_right_inverse
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T04:53:14.057505+00:00
-- url     : https://prove2.me/submissions/f1effd4c-25e2-408e-91e7-aacc046eb61e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_scaled_truncated_matrix_surjective
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_packet_matrix_surjectivity_gives_right_inverse
open Filter Topology
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
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∃ F : (Row d ((n : Real) * (R : Real)) → Complex) →
          WeightedPolynomial d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d))
            ((n : Real) * (R : Real)),
        ∀ y : Row d ((n : Real) * (R : Real)) → Complex,
          packetMap d ((n : Real) * (R : Real)) (F y) = y := by
  obtain ⟨N, hN⟩ := eventual_scaled_truncated_matrix_surjective
    nu hnu d R T e hR he hT hscale
  refine ⟨N, fun n hn => ?_⟩
  exact packet_matrix_surjectivity_gives_right_inverse nu d
    ((n : Real) * (R : Real)) T hT (hN n hn)