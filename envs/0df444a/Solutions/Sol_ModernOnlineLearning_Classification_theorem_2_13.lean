-- Prove2me | solution 1 for ModernOnlineLearning.Classification.theorem_2_13
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T04:04:34.511119+00:00
-- url     : https://prove2.me/submissions/dae18ae7-9afd-4f0d-a5ed-21739f122815

import Definitions.Def_ModernOnlineLearning_Adaptive_Defs
set_option autoImplicit false

theorem solution {d : ℕ} (T : ℕ) (η : ℝ) (hη : 0 < η)
    (g x : ℕ → ModernOnlineLearning.Adaptive.Vec d)
    (hrun : ∀ t ∈ Finset.Icc 1 T, x (t + 1) = x t - η • g t)
    (u : ModernOnlineLearning.Adaptive.Vec d) :
    (∑ t ∈ Finset.Icc 1 T, inner ℝ (g t) (x t - u)) ≤
      ‖u - x 1‖ ^ 2 / (2 * η) +
        η / 2 * (∑ t ∈ Finset.Icc 1 T, ‖g t‖ ^ 2) -
        ‖x (T + 1) - u‖ ^ 2 / (2 * η) := by
  induction T with
  | zero => simp [norm_sub_rev]
  | succ n ih =>
    have hn : ∀ t ∈ Finset.Icc 1 n, x (t + 1) = x t - η • g t := by
      intro t ht
      apply hrun
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ht).1, Nat.le_trans (Finset.mem_Icc.mp ht).2 (Nat.le_succ n)⟩
    have hprev := ih hn
    have hnext := hrun (n + 1) (by simp)
    have heq : x (n + 1) - η • g (n + 1) - u =
        (x (n + 1) - u) - η • g (n + 1) := by abel
    have hs : ‖x (n + 1 + 1) - u‖ ^ 2 =
        ‖x (n + 1) - u‖ ^ 2 - 2 * η * inner ℝ (g (n + 1)) (x (n + 1) - u) +
          η ^ 2 * ‖g (n + 1)‖ ^ 2 := by
      rw [hnext, heq, norm_sub_sq_real, real_inner_smul_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos hη, real_inner_comm (x (n + 1) - u)]
      ring
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    have hstep : inner ℝ (g (n + 1)) (x (n + 1) - u) =
        ‖x (n + 1) - u‖ ^ 2 / (2 * η) + η / 2 * ‖g (n + 1)‖ ^ 2 -
          ‖x (n + 1 + 1) - u‖ ^ 2 / (2 * η) := by
      field_simp
      nlinarith
    linarith

