-- Prove2me | solution 1 for GoldenRatioVI.Explicit.zbar_identity
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:16:22.02821+00:00
-- url     : https://prove2.me/submissions/04ca5080-2c2e-48c5-9030-68fe12b9fe1c

import Definitions.Def_GoldenRatioVI_Explicit_egraalRun

open scoped RealInnerProductSpace
open GoldenRatioVI.Explicit

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ)
    (hrun : IsEGRAALRun g F ϕ lamBar z zbar lam theta) (u : E) (k : ℕ) :
    ‖z (k + 1) - u‖ ^ 2 =
      ϕ / (ϕ - 1) * ‖zbar (k + 1) - u‖ ^ 2 - 1 / (ϕ - 1) * ‖zbar k - u‖ ^ 2
        + 1 / ϕ * ‖z (k + 1) - zbar k‖ ^ 2 := by
  have hp : ϕ ≠ 0 := by linarith [hrun.one_lt_phi]
  have hp1 : ϕ-1 ≠ 0 := by linarith [hrun.one_lt_phi]
  rw [hrun.zbar_succ]
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm (zbar k) (z (k+1)), real_inner_comm u (z (k+1)),
    real_inner_comm u (zbar k)]
  field_simp
  <;> ring

