-- Prove2me | solution 1 for Mdp.DiscountedMDP.valueIteration_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:45:38.997972+00:00
-- url     : https://prove2.me/submissions/20479b2f-451f-450e-b5cf-be985408cdc5

import Definitions.Def_Mdp_ValueIteration
import Definitions.Def_Mdp_ValueIterationAlgorithm
import Theorems.Thm_Mdp_DiscountedMDP_numIters_spec
import Theorems.Thm_Mdp_DiscountedMDP_bellman_aposteriori_bound
import Theorems.Thm_Mdp_DiscountedMDP_bellman_contracting
import Theorems.Thm_Mdp_DiscountedMDP_vOpt_fixedPoint


set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)
namespace Mdp.DiscountedMDP
theorem _root_.solution {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) :
    2 * dist (M.valueIteration eps v) M.vOpt < eps := by
  have hval : M.valueIteration eps v = M.bellman^[M.numIters heps v + 1] v := by
    simp only [valueIteration, dif_pos heps]
  have hstop : 2 * M.l * dist (M.bellman^[M.numIters heps v + 1] v)
      (M.bellman^[M.numIters heps v] v) < eps * (1 - M.l) :=
    M.numIters_spec heps v
  set N := M.numIters heps v
  set w := M.bellman^[N] v with hw
  have hbw : M.bellman^[N + 1] v = M.bellman w := by
    rw [hw]; exact Function.iterate_succ_apply' M.bellman N v
  rw [hbw] at hval hstop
  rw [dist_comm (M.bellman w) w] at hstop
  rw [hval]
  have hlcast : (M.lNN : ℝ) = M.l := rfl
  have hbound : dist w M.vOpt ≤ dist w (M.bellman w) / (1 - M.l) := by
    have h0 := M.bellman_aposteriori_bound w 0
    simp only [Function.iterate_zero_apply, zero_add, Function.iterate_one] at h0
    rwa [hlcast] at h0
  have hopt_move : dist w M.vOpt * (1 - M.l) ≤ dist w (M.bellman w) := by
    rw [le_div_iff₀ (by linarith [M.l_lt_one] : (0 : ℝ) < 1 - M.l)] at hbound
    exact hbound
  have hcontract : dist (M.bellman w) M.vOpt ≤ M.l * dist w M.vOpt := by
    have h1 := M.bellman_contracting w M.vOpt
    rwa [M.vOpt_fixedPoint] at h1
  have step1 : (2 * M.l * dist w M.vOpt) * (1 - M.l) ≤ 2 * M.l * dist w (M.bellman w) := by
    nlinarith [hopt_move, M.l_nonneg]
  have step2 : (2 * M.l * dist w M.vOpt) * (1 - M.l) < eps * (1 - M.l) := by
    nlinarith [step1, hstop]
  have step3 : 2 * M.l * dist w M.vOpt < eps :=
    lt_of_mul_lt_mul_right step2 (by linarith [M.l_lt_one] : (0 : ℝ) ≤ 1 - M.l)
  linarith [hcontract, step3]
end Mdp.DiscountedMDP
