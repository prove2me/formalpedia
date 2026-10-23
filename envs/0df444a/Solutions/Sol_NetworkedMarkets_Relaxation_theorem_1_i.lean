-- Prove2me | solution 1 for NetworkedMarkets.Relaxation.theorem_1_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:47:23.6394+00:00
-- url     : https://prove2.me/submissions/2c40c519-4fde-4aa7-8825-1be47cdd385a

import Mathlib
import Definitions.Def_NetworkedMarkets_Relaxation_Setting
import Theorems.Thm_NetworkedMarkets_Relaxation_eq_6_revenue_bound
import Theorems.Thm_NetworkedMarkets_Relaxation_proposition_EC_1_iv
import Theorems.Thm_NetworkedMarkets_Relaxation_proposition_EC_1_iii
import Theorems.Thm_NetworkedMarkets_Relaxation_step_i_2_subscription_implementation

open Filter Topology

open NetworkedMarkets.Relaxation in
theorem solution {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : M.Standing)
    (xbar : S → B → ℝ) (qsbar : S → ℝ) (qbbar : B → ℝ) (hopt : M.IsOpt7 xbar qsbar qbbar) :
    IsGreatest M.Value3 (M.h qsbar qbbar) ∧
      ∀ (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ),
        M.Feas3 f p x qs qb → M.rev f p x = M.h qsbar qbbar → qs = qsbar ∧ qb = qbbar := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨θb, θs, ηb, ηs, π, hd⟩ := proposition_EC_1_iii M hM xbar qsbar qbbar hopt
    obtain ⟨hU, hCE, hrev⟩ :=
      step_i_2_subscription_implementation M hM xbar qsbar qbbar hopt θb θs ηb ηs π hd
    exact ⟨_, θs, xbar, qsbar, qbbar, ⟨hU, hCE⟩, hrev.symm⟩
  · rintro v ⟨f, p, x, qs, qb, h3, rfl⟩
    obtain ⟨h7, hle⟩ := eq_6_revenue_bound M hM.1 f p x qs qb h3
    exact le_trans hle (hopt.2 x qs qb h7)
  · intro f p x qs qb h3 hrev
    obtain ⟨h7, hle⟩ := eq_6_revenue_bound M hM.1 f p x qs qb h3
    have hopt' : M.IsOpt7 x qs qb := by
      refine ⟨h7, fun x' qs' qb' h7' => ?_⟩
      have := hopt.2 x' qs' qb' h7'
      linarith
    exact proposition_EC_1_iv M hM x qs qb xbar qsbar qbbar hopt' hopt
