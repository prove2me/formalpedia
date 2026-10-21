-- Prove2me | solution 1 for ModernOnlineLearning.FTRL.lemma_7_1
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T17:06:52.254221+00:00
-- url     : https://prove2.me/submissions/23dd57ec-78b6-4694-a77b-9c081947e36a

import Definitions.Def_ModernOnlineLearning_FTRL_Defs

set_option autoImplicit false
open scoped BigOperators
open ModernOnlineLearning.FTRL

private lemma telescope (f : ℕ → ℝ) (n : ℕ) :
    (∑ t ∈ Finset.Icc 1 n, (f t - f (t + 1))) = f 1 - f (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (hVclosed : IsClosed V) (hVnonempty : V.Nonempty)
    (ψ ℓ : ℕ → E → ℝ) (x : ℕ → E) (T : ℕ)
    (hRun : IsFTRLRunUpTo V ψ ℓ x T) (u : E) :
    (∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u)) =
      ψ (T + 1) u - ψ 1 (x 1) +
      (∑ t ∈ Finset.Icc 1 T,
        (F ψ ℓ t (x t) - F ψ ℓ (t + 1) (x (t + 1)) + ℓ t (x t))) +
      F ψ ℓ (T + 1) (x (T + 1)) - F ψ ℓ (T + 1) u := by
  rw [Finset.sum_add_distrib, telescope (fun t => F ψ ℓ t (x t)), Finset.sum_sub_distrib]
  simp only [F, Finset.Ico_self, Finset.sum_empty, add_zero,
    Finset.Ico_add_one_right_eq_Icc]
  ring

