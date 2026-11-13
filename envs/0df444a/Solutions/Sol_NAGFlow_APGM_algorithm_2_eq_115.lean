-- Prove2me | solution 1 for NAGFlow.APGM.algorithm_2_eq_115
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-12T13:32:54.962311+00:00
-- url     : https://prove2.me/submissions/5b4f1831-0fb2-4274-8979-3e5e53d4f78f

import Definitions.Def_NAGFlow_APGM_Setting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

open NAGFlow.APGM

theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (gradh : V → V) (g : V → ℝ) (D : Set V) (μ L : ℝ) (hμ : 0 ≤ μ) (hL : 0 < L)
    (α γ : ℕ → ℝ) (x y w v : ℕ → V) (hrun : IsAPGMRun gradh g D μ L α γ x y w v) :
    IsSemiImplicitRun gradh g D μ L α γ x y v := by
  have hgpos : ∀ k, 0 < γ k := by
    intro k
    induction k with
    | zero => exact hrun.gamma0_pos
    | succ k ih =>
      rw [hrun.gamma_eq k]
      exact div_pos (add_pos_of_pos_of_nonneg ih (mul_nonneg hμ (hrun.alpha_pos k).le))
        (by linarith [hrun.alpha_pos k])
  refine ⟨hrun.gamma0_pos, hrun.alpha_pos, ?_, hrun.x_eq, ?_, ?_⟩
  · intro k
    rw [hrun.y_eq k]
    have ha := ne_of_gt (hrun.alpha_pos k)
    have hp : (1 + α k) ≠ 0 := ne_of_gt (by linarith [hrun.alpha_pos k])
    match_scalars <;> field_simp [ha, hp] <;> ring
  · intro k
    have ha := ne_of_gt (hrun.alpha_pos k)
    have hg := ne_of_gt (hgpos k)
    have hp : (1 + α k) ≠ 0 := ne_of_gt (by linarith [hrun.alpha_pos k])
    have hsum : γ k + μ * α k ≠ 0 := ne_of_gt
      (add_pos_of_pos_of_nonneg (hgpos k) (mul_nonneg hμ (hrun.alpha_pos k).le))
    have hsum2 : γ k + α k * μ ≠ 0 := by simpa only [mul_comm] using hsum
    have hstep := congrArg (fun t : ℝ => t * (γ k + α k * μ)) (hrun.step_rel k)
    rw [hrun.v_eq k, hrun.w_eq k, hrun.gamma_eq k]
    simp only [gradMap, one_div_one_div]
    match_scalars <;> field_simp [ha, hg, hp, hsum, hsum2] <;> nlinarith only [hstep]
  · intro k
    have ha := ne_of_gt (hrun.alpha_pos k)
    have hp : (1 + α k) ≠ 0 := ne_of_gt (by linarith [hrun.alpha_pos k])
    rw [hrun.gamma_eq k]
    field_simp [ha, hp]
    ring

#print axioms solution


