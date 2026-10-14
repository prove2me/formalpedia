-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.equal_truncated_packets_implies_ideal_power
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T05:51:31.07508+00:00
-- url     : https://prove2.me/submissions/40b23c3b-2697-4440-85f1-10dacb3788a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_zero_truncated_packet_implies_ideal_power

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
    (n : Nat) (P Q : MvPolynomial (Fin (d.m + 1)) Complex)
    (hpacket :
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T P =
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T Q) :
    P - Q ∈ (logarithmicCentersIdeal
      (fun j : Fin d.K => fun i => (j.val : Complex) *
        MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
      T e) ^ n := by
  classical
  let w := MatrixArithmetic.logWeights (finiteDenominators d)
  let r := MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)
  have hzero : truncatedPolynomialPacket d.K d.v0 d.base.theta w
      ((n : Real) * (R : Real)) r T (P - Q) = 0 := by
    funext rho
    simp only [truncatedPolynomialPacket, map_sub]
    exact sub_eq_zero.mpr (congrFun hpacket rho)
  have hw : ∀ i, 0 < w i := by
    intro i
    change 0 < (Nat.ceil (Real.log (d.q i.val)) : Real)
    rw [← d.x_log]
    exact lt_of_lt_of_le zero_lt_one (d.x_one_le _)
  have hscale' : ∀ i : Fin (d.m + 1), (R : Real) ≤ (e i : Real) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta w i := by
    intro i
    rw [hscale i]
  have hmem := OAI.PiExponent.FormalInterpolation.zero_truncated_packet_implies_ideal_power
    (m := d.m) (K := d.K) d.v0 d.base.theta w (R : Real) r T e
    d.v0_pos d.base.theta_pos hw (by exact_mod_cast hR) he hT hscale' n (P - Q) hzero
  simpa [w, r] using hmem
