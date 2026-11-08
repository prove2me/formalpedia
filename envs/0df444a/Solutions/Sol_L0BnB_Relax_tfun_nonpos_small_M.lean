-- Prove2me | solution 1 for L0BnB.Relax.tfun_nonpos_small_M
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:09:04.825865+00:00
-- url     : https://prove2.me/submissions/87e920be-f153-4267-9692-c72fbc25e7e2

import Mathlib
import Definitions.Def_L0BnB_Relax_tfun

open L0BnB.Relax in
theorem solution (lam0 lam2 M b : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2)
    (hM : M ≤ 1 / 2 * Real.sqrt (lam0 / lam2)) (hb : |b| ≤ M) :
    tfun lam0 lam2 M b = (2 * Real.sqrt (lam0 * lam2) - lam0 / M) * |b| - lam2 * b ^ 2 ∧
      tfun lam0 lam2 M b ≤ 0 := by
  have hs0 : 0 ≤ Real.sqrt (lam2 / lam0) := Real.sqrt_nonneg _
  have ht0 : 0 ≤ Real.sqrt (lam0 / lam2) := Real.sqrt_nonneg _
  have hst : Real.sqrt (lam2 / lam0) * Real.sqrt (lam0 / lam2) = 1 := by
    rw [← Real.sqrt_mul (div_nonneg h2.le h0.le)]
    have : lam2 / lam0 * (lam0 / lam2) = 1 := by
      rw [div_mul_div_comm, mul_comm lam2 lam0, div_self (mul_pos h0 h2).ne']
    rw [this, Real.sqrt_one]
  have key : Real.sqrt (lam0 * lam2) = lam0 * Real.sqrt (lam2 / lam0) := by
    have e : lam0 * lam2 = lam0 ^ 2 * (lam2 / lam0) := by
      rw [sq, mul_assoc, mul_div_cancel₀ _ h0.ne']
    rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h0.le]
  have hbabs : 0 ≤ |b| := abs_nonneg b
  have hbs : |b * Real.sqrt (lam2 / lam0)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hs0]
    have h1 : |b| * Real.sqrt (lam2 / lam0) ≤ (1 / 2 * Real.sqrt (lam0 / lam2)) *
        Real.sqrt (lam2 / lam0) :=
      mul_le_mul_of_nonneg_right (hb.trans hM) hs0
    have h3 : (1 / 2 * Real.sqrt (lam0 / lam2)) * Real.sqrt (lam2 / lam0) = 1 / 2 := by
      rw [mul_assoc, mul_comm (Real.sqrt (lam0 / lam2)), hst, mul_one]
    linarith
  have part1 : tfun lam0 lam2 M b =
      (2 * Real.sqrt (lam0 * lam2) - lam0 / M) * |b| - lam2 * b ^ 2 := by
    unfold tfun reverseHuber
    rw [if_pos hbs, abs_mul, abs_of_nonneg hs0, key]
    ring
  refine ⟨part1, ?_⟩
  rw [part1]
  rcases le_or_gt M 0 with hM0 | hM0
  · have hb0 : |b| = 0 := le_antisymm (hb.trans hM0) hbabs
    have hb0' : b = 0 := abs_eq_zero.mp hb0
    rw [hb0, hb0']
    simp
  · have hq : 2 * Real.sqrt (lam0 * lam2) ≤ lam0 / M := by
      rw [le_div_iff₀ hM0, key]
      have hA : 0 ≤ 2 * (lam0 * Real.sqrt (lam2 / lam0)) := by positivity
      have h4 := mul_le_mul_of_nonneg_left hM hA
      have h5 : lam0 * (Real.sqrt (lam2 / lam0) * Real.sqrt (lam0 / lam2)) = lam0 := by
        rw [hst, mul_one]
      nlinarith
    have h6 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hq) hbabs
    nlinarith [mul_nonneg h2.le (sq_nonneg b)]
