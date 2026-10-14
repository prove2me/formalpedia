-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eventual_scaled_truncated_matrix_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T05:06:02.521699+00:00
-- url     : https://prove2.me/submissions/6bdeb9b0-e8f3-450c-b80c-a2026a93d913
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_logarithmic_ideal_bounded_representatives
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_truncated_polynomial_jets_surjective
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_ideal_power_truncated_packet_vanishing
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_truncated_packet_matrix_representation

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
  classical
  have hw : ∀ i, 0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
    intro i
    change 0 < (Nat.ceil (Real.log (d.q i.val)) : Real)
    rw [← d.x_log]
    exact lt_of_lt_of_le zero_lt_one (d.x_one_le _)
  have hcenters : Function.Injective (fun j : Fin d.K => fun i : Fin d.m =>
      (j.val : Complex) * MatrixArithmetic.rationalCenters
        (finiteNumerators d) (finiteDenominators d) i) := by
    let i : Fin d.m := ⟨0, by have := d.m_pos; omega⟩
    have hp : (finiteNumerators d i : Complex) ≠ 0 := by
      exact_mod_cast (d.approximations i.val).2.1
    have hq : (finiteDenominators d i : Complex) ≠ 0 := by
      have hqNat : finiteDenominators d i ≠ 0 := by
        have := (d.approximations i.val).1
        change d.q i.val ≠ 0
        omega
      exact_mod_cast hqNat
    have hr : MatrixArithmetic.rationalCenters
        (finiteNumerators d) (finiteDenominators d) i ≠ 0 := by
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hp) hq
    intro j k hjk
    have hc : (j.val : Complex) = (k.val : Complex) :=
      (mul_right_cancel₀ hr) (congrFun hjk i)
    apply Fin.ext
    exact_mod_cast hc
  obtain ⟨N, hrep⟩ := eventual_logarithmic_ideal_bounded_representatives
    nu hnu d R T e hR he hT hscale
  refine ⟨N, ?_⟩
  intro n hn y
  obtain ⟨P, hP⟩ := finite_truncated_polynomial_jets_surjective
    d.K d.v0 d.base.theta (MatrixArithmetic.logWeights (finiteDenominators d))
    ((n : Real) * (R : Real))
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    T hcenters y
  obtain ⟨Q, hQ⟩ := hrep n hn P
  have hz := logarithmic_ideal_power_truncated_packet_vanishing
    d.K d.v0 d.base.theta (MatrixArithmetic.logWeights (finiteDenominators d))
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    (R : Real) T e d.v0_pos d.base.theta_pos hw (by exact_mod_cast hR)
    (fun i => le_of_eq (hscale i)) n (P - Q.val) hQ
  have hpacket : truncatedPolynomialPacket d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
      T Q.val = y := by
    funext rho
    have hzrho := congrFun hz rho
    simp only [truncatedPolynomialPacket, map_sub] at hzrho
    have hPrho := congrFun hP rho
    change _ = y rho
    exact (sub_eq_zero.mp hzrho).symm.trans hPrho
  obtain ⟨x, hx⟩ := bounded_truncated_packet_matrix_representation
    d.K d.w0 d.v0 d.base.theta (MatrixArithmetic.logWeights (finiteDenominators d))
    ((n : Real) * (R : Real))
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    T d.w0_pos hw Q
  exact ⟨x, hx.symm.trans hpacket⟩
