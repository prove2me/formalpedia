-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.eventual_scaled_truncated_matrix_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T14:44:14.951157+00:00
-- url     : https://prove2.me/submissions/33f02722-5b08-4478-9b70-edad2d0f87e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_truncated_packet_matrix_representation
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_bounded_truncated_packet_surjective

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
      Function.Surjective
        (InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d))
          ((n : Real) * (R : Real))
          (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
          T).mulVecLin := by
  obtain ⟨N, hpacket⟩ :=
    OAI.PiExponent.FormalInterpolation.eventual_bounded_truncated_packet_surjective
      nu hnu d R T e hR he hT hscale
  refine ⟨N, ?_⟩
  intro n hn y
  obtain ⟨P, hP⟩ := hpacket n hn y
  obtain ⟨x, hx⟩ :=
    OAI.PiExponent.FormalInterpolation.bounded_truncated_packet_matrix_representation
      d.K d.w0 d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d))
      ((n : Real) * (R : Real))
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
      T d.w0_pos
      (by
        intro i
        change 0 < (Nat.ceil (Real.log (d.q i.val)) : Real)
        rw [← d.x_log]
        exact lt_of_lt_of_le zero_lt_one (d.x_one_le _))
      P
  exact ⟨x, hx.symm.trans hP⟩