-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.eventual_scaled_packets
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-12T20:18:21.771993+00:00
-- url     : https://prove2.me/submissions/ba471c30-2cf9-442c-952b-68263d719f4c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_eventual_bounded_representatives
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_ideal_power_packet_vanishing
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_raw_packets_surjective

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals


theorem solution (nu : ℝ) (hnu : 2 < nu) (d : FixedData nu) :
    ∃ R : ℚ, 0 < R ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Function.Surjective (packetMap d.K d.w0 d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * (R : ℝ))
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))) := by
  obtain ⟨R, hR, T, e, N, he, hT, hrep⟩ := eventual_bounded_representatives d
  have hw : ∀ i, 0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
    intro i
    change 0 < (Nat.ceil (Real.log (d.q i.val)) : ℝ)
    rw [← d.x_log]
    exact lt_of_lt_of_le zero_lt_one (d.x_one_le _)
  have hcenters : Function.Injective (fun j : Fin d.K => fun i : Fin d.m =>
      (j.val : ℂ) * MatrixArithmetic.rationalCenters
        (finiteNumerators d) (finiteDenominators d) i) := by
    let i : Fin d.m := ⟨0, by have := d.m_pos; omega⟩
    have hp : (finiteNumerators d i : ℂ) ≠ 0 := by
      exact_mod_cast (d.approximations i.val).2.1
    have hq : (finiteDenominators d i : ℂ) ≠ 0 := by
      have hqNat : finiteDenominators d i ≠ 0 := by
        have := (d.approximations i.val).1
        change d.q i.val ≠ 0
        omega
      exact_mod_cast hqNat
    have hr : MatrixArithmetic.rationalCenters
        (finiteNumerators d) (finiteDenominators d) i ≠ 0 := by
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hp) hq
    intro j k hjk
    have hc : (j.val : ℂ) = (k.val : ℂ) :=
      (mul_right_cancel₀ hr) (congrFun hjk i)
    apply Fin.ext
    exact_mod_cast hc
  refine ⟨R, hR, N, ?_⟩
  intro n hn y
  obtain ⟨P, hP⟩ := raw_packets_surjective d.K d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * (R : ℝ))
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    d.v0_pos d.base.theta_pos hw hcenters y
  obtain ⟨Q, hQ⟩ := hrep n hn P
  have hz := ideal_power_packet_vanishing d.K d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d))
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    (R : ℝ) T e d.v0_pos d.base.theta_pos hw (by exact_mod_cast hR)
    he hT n (P - Q.val) hQ
  refine ⟨Q, ?_⟩
  funext rho
  have hzrho := congrFun hz rho
  simp only [rawPacketMap, map_sub, Pi.zero_apply] at hzrho
  have hPrho := congrFun hP rho
  change _ = y rho
  exact (sub_eq_zero.mp hzrho).symm.trans hPrho
