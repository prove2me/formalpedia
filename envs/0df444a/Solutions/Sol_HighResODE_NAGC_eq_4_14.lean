-- Prove2me | solution 1 for HighResODE.NAGC.eq_4_14
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:52:37.32451+00:00
-- url     : https://prove2.me/submissions/c953b84f-b22d-4b52-84a5-3348a4c78c3f

import Mathlib
import Definitions.Def_HighResODE_NAGC_Setting

open scoped InnerProductSpace

open HighResODE.NAGC in
theorem solution {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (s : ℝ) (hs : 0 < s) (x y : ℕ → HighResODE.NAGSC.E n) (hrun : IsNAGC f s x y) (xs : HighResODE.NAGSC.E n) (k : ℕ) :
    lyap f s xs x (k + 1) - lyap f s xs x k
      = s * ((k : ℝ) + 3) * ((k : ℝ) + 1) * (f (x (k + 1)) - f (x k))
        - s ^ ((3 : ℝ) / 2) * ((k : ℝ) + 3) * ((k : ℝ) + 4)
            * ⟪gradient f (x (k + 1)), HighResODE.NAGSC.vel s x (k + 1)⟫_ℝ
        + s * (2 * (k : ℝ) + 5) * (f (x (k + 1)) - f xs)
        - s * (2 * (k : ℝ) + 6) * ⟪gradient f (x (k + 1)), x (k + 1) - xs⟫_ℝ
        - s ^ 2 * ((k : ℝ) + 3) * (3 * (k : ℝ) + 7) / 2 * ‖gradient f (x (k + 1))‖ ^ 2 := by
  set r := Real.sqrt s with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr hs
  have hrr : r * r = s := Real.mul_self_sqrt hs.le
  set g := gradient f with hg
  set W : ℕ → HighResODE.NAGSC.E n := fun j =>
    (((j : ℝ) + 1) * r) • HighResODE.NAGSC.vel s x j + (2 : ℝ) • (x (j + 1) - xs)
      + (((j : ℝ) + 1) * s) • g (x j) with hWdef
  have hL : ∀ j, lyap f s xs x j
      = s * ((j : ℝ) + 3) * ((j : ℝ) + 1) * (f (x j) - f xs) + 1 / 2 * ‖W j‖ ^ 2 :=
    fun j => rfl
  have hv : ∀ j (c : ℝ), (c * r) • HighResODE.NAGSC.vel s x j = c • (x (j + 1) - x j) := by
    intro j c
    unfold HighResODE.NAGSC.vel
    rw [smul_smul, ← hrdef]
    congr 1
    field_simp
  have hy1 := hrun.step_y k
  have hy2 := hrun.step_y (k + 1)
  have hx2 := hrun.step_x (k + 1)
  have hc : ((k : ℝ) + 4) * (((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) + 3)) = (k : ℝ) + 1 := by
    push_cast
    field_simp
    ring
  have hx2' : ((k : ℝ) + 4) • x (k + 1 + 1)
      = ((2 : ℝ) * k + 5) • y (k + 1 + 1) - ((k : ℝ) + 1) • y (k + 1) := by
    rw [hx2, smul_add, smul_smul, hc]
    module
  have hW : W k = W (k + 1) + (((k : ℝ) + 3) * s) • g (x (k + 1)) := by
    simp only [hWdef]
    rw [hv, hv]
    push_cast
    linear_combination (norm := module) -(hx2' + ((2 : ℝ) * k + 5) • hy2 - ((k : ℝ) + 1) • hy1)
  have hW' : W (k + 1) = (((k : ℝ) + 4) * r) • HighResODE.NAGSC.vel s x (k + 1)
      + (2 : ℝ) • (x (k + 1) - xs) + (((k : ℝ) + 2) * s) • g (x (k + 1)) := by
    simp only [hWdef]
    rw [hv, hv]
    push_cast
    module
  have hs32 : s ^ ((3 : ℝ) / 2) = s * r := by
    rw [hrdef, Real.sqrt_eq_rpow, ← Real.rpow_one_add' hs.le (by norm_num)]
    norm_num
  rw [hL, hL]
  clear_value W
  rw [hW, norm_add_sq_real, hW', hs32]
  push_cast
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_comm (g (x (k + 1))), real_inner_self_eq_norm_sq, RCLike.conj_to_real]
  rw [← hrr]
  ring
