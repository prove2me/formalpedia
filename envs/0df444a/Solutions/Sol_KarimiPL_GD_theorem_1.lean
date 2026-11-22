-- Prove2me | solution 1 for KarimiPL.GD.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-11T00:48:25.164089+00:00
-- url     : https://prove2.me/submissions/91669052-1095-479a-940d-e24e143b0491

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
import Theorems.Thm_ShiOptRates_pl_step
import Theorems.Thm_KarimiPL_GD_quadUpper_of_lipschitz

open scoped InnerProductSpace

set_option autoImplicit false

theorem solution {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hdiff : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ y, f xstar ≤ f y)
    (mu : ℝ) (hmu : 0 < mu)
    (hPL : ShiOptRates.PolyakLojasiewicz f (gradient f) mu (f xstar))
    (x : ℕ → EuclideanSpace ℝ (Fin d))
    (hx : ∀ k, x (k + 1) = x k - (1 / L) • gradient f (x k)) :
    ∀ k : ℕ, f (x k) - f xstar ≤ (1 - mu / L) ^ k * (f (x 0) - f xstar) := by
  -- Step A (ACCEPTED 2026-10-10, submission 56e796e9): Lipschitz gradient
  -- implies the quadratic upper bound.
  have hQ : ShiOptRates.QuadUpper f (gradient f) L :=
    KarimiPL.GD.quadUpper_of_lipschitz f hdiff L hLip
  -- One-step contraction from the proved pl_step with δ = 0 and the GD update.
  have hstep : ∀ k, f (x (k + 1)) - f xstar
      ≤ (1 - mu / L) * (f (x k) - f xstar) := by
    intro k
    have herr : ‖gradient f (x k) - gradient f (x k)‖ ≤ (0 : ℝ) := by simp
    have h := ShiOptRates.pl_step (E := EuclideanSpace ℝ (Fin d)) (f := f)
      (g := gradient f) (L := L) (mu := mu) (fstar := f xstar)
      hL hmu hQ hPL (x k) (gradient f (x k)) (δ := 0) herr
    have h1 : (1 : ℝ) / L = L⁻¹ := by rw [div_eq_mul_inv, one_mul]
    have hLinv : x k - L⁻¹ • gradient f (x k) = x (k + 1) := by
      rw [← h1, ← hx k]
    rw [hLinv] at h
    have hz : (0 : ℝ) ^ 2 / (2 * L) = 0 := by norm_num
    rw [hz, add_zero] at h
    exact h
  -- Degenerate probe (triage §3): the induction multiply-step needs
  -- 0 ≤ 1 - μ/L, which is forced by the hypotheses unless f is constant.
  by_cases hle : mu ≤ L
  · -- Main case: μ ≤ L, so the contraction factor is nonnegative.
    have hnn : (0 : ℝ) ≤ 1 - mu / L := by
      have h1 : mu / L ≤ 1 := (div_le_one hL).mpr hle
      linarith
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc f (x (k + 1)) - f xstar
          ≤ (1 - mu / L) * (f (x k) - f xstar) := hstep k
        _ ≤ (1 - mu / L) * ((1 - mu / L) ^ k * (f (x 0) - f xstar)) :=
            mul_le_mul_of_nonneg_left ih hnn
        _ = (1 - mu / L) ^ (k + 1) * (f (x 0) - f xstar) := by
            rw [pow_succ]; ring
  · -- μ > L: vacuous unless f is constant, in which case every gap is 0.
    push_neg at hle
    by_cases hex : ∃ z, f xstar < f z
    · -- Non-minimizer witness: one pl_step gives a negative upper bound,
      -- contradicting the global minimality of xstar.
      obtain ⟨z, hzwit⟩ := hex
      have herr : ‖gradient f z - gradient f z‖ ≤ (0 : ℝ) := by simp
      have h := ShiOptRates.pl_step (E := EuclideanSpace ℝ (Fin d)) (f := f)
        (g := gradient f) (L := L) (mu := mu) (fstar := f xstar)
        hL hmu hQ hPL z (gradient f z) (δ := 0) herr
      have hneg : (1 : ℝ) - mu / L < 0 := by
        have hlt : (1 : ℝ) < mu / L := (one_lt_div hL).mpr hle
        linarith
      have hpos : (0 : ℝ) < f z - f xstar := sub_pos.mpr hzwit
      have hz : (0 : ℝ) ^ 2 / (2 * L) = 0 := by norm_num
      have hge : (0 : ℝ) ≤ f (z - L⁻¹ • gradient f z) - f xstar :=
        sub_nonneg.mpr (hxstar _)
      have hlt : (1 - mu / L) * (f z - f xstar) + (0 : ℝ) ^ 2 / (2 * L) < 0 := by
        rw [hz, add_zero]
        exact mul_neg_of_neg_of_pos hneg hpos
      linarith
    · -- f is constant: every gap is 0 and (1 - μ/L)^k * 0 = 0.
      push_neg at hex
      intro k
      have hk : f (x k) = f xstar := le_antisymm (hex _) (hxstar _)
      have hk0 : f (x 0) = f xstar := le_antisymm (hex _) (hxstar _)
      rw [hk, hk0, sub_self, mul_zero]
