-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.global_interpolation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T19:41:28.196126+00:00
-- url     : https://prove2.me/submissions/74da2c65-1f0f-43ef-9028-b13c4ff66951
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_packet_interpolation
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_matrix_surjective_of_packets
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

open Filter Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution : GlobalInterpolationStatement := by
  intro nu hnu d L
  have hT : ∀ i : Fin d.m,
      MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ) ≤
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
          (d.v0 : ℝ) := by
    intro i
    have hw : 0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
      change 0 < (⌈Real.log (d.q i.val)⌉₊ : ℝ)
      rw [← d.x_log i.val]
      exact lt_of_lt_of_le zero_lt_one (d.x_one_le _)
    have hF : 1 / (d.base.theta : ℝ) < d.F0 :=
      (div_lt_div_of_pos_right (by norm_num : (1 : ℝ) < 2)
        d.base.theta_pos).trans d.F0_large
    have hc := Nat.le_ceil
      (d.F0 * MatrixArithmetic.logWeights (finiteDenominators d) i / (d.v0 : ℝ))
    calc
      _ = (1 / (d.base.theta : ℝ)) *
          MatrixArithmetic.logWeights (finiteDenominators d) i := by ring
      _ ≤ d.F0 * MatrixArithmetic.logWeights (finiteDenominators d) i :=
        mul_le_mul_of_nonneg_right hF.le hw.le
      _ ≤ _ := (div_le_iff₀ d.v0_pos).mp hc
  obtain ⟨R, hR, hp⟩ := FormalInterpolation.eventual_packet_interpolation nu hnu d
  obtain ⟨N, hN⟩ := eventually_atTop.mp hp
  let n : ℕ := max N (Nat.ceil (L / (R : ℝ)))
  have hRreal : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hL : L ≤ (n : ℝ) * (R : ℝ) := by
    apply (div_le_iff₀ hRreal).mp
    exact (Nat.le_ceil _).trans (by exact_mod_cast
      (le_max_right N (Nat.ceil (L / (R : ℝ)))))
  refine ⟨(n : ℝ) * (R : ℝ), hL, ?_⟩
  have hcast : (((n : ℚ) * R : ℚ) : ℝ) = (n : ℝ) * (R : ℝ) := by
    push_cast
    rfl
  have hp' : Function.Surjective
      (FormalInterpolation.packetMap d (((n : ℚ) * R : ℚ) : ℝ)) := by
    rw [hcast]
    exact hN n (le_max_left _ _)
  have hs := FormalInterpolation.matrix_surjective_of_packets d ((n : ℚ) * R) hT hp'
  rw [hcast] at hs
  exact hs
