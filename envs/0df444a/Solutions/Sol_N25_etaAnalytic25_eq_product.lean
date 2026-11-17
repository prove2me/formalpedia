-- Prove2me | solution 1 for N25.etaAnalytic25_eq_product
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:34.936122+00:00
-- url     : https://prove2.me/submissions/19d08dae-96bd-4e70-a9da-3411ab33ae11

import Mathlib
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace N25

private theorem multipliable_residue_factors (q : ℂ) (hq : ‖q‖ < 1)
    (a : ℕ → ℕ) (ha : ∀ n, n ≤ a n) :
    Multipliable (fun n : ℕ => 1 - q ^ (a n)) := by
  have hs : Summable (fun n : ℕ => ‖-(q ^ (a n))‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (summable_geometric_of_lt_one (norm_nonneg q) hq)
    rw [norm_neg, norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg q) hq.le (ha n)
  simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable hs

/-- At the level-25 dilation, the literal Siegel factor is its exponential prefactor times two residue streams. -/
theorem _root_.solution
    (g : ℕ) (hg : 0 < g) (hg25 : g < 25)
    (τ : UpperHalfPlane) :
    etaAnalytic25 g τ =
      Complex.exp (Real.pi * Complex.I *
        (((g : ℂ) / 25) ^ 2 - (g : ℂ) / 25 + 1 / 6) * (25 * (τ : ℂ))) *
      (∏' n : ℕ,
        (1 - Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ (25 * n + g)) *
        (1 - Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ (25 * (n + 1) - g))) := by
  let q := Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ))
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have hq : ‖q‖ < 1 := by
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    have hp := mul_pos Real.pi_pos τ.im_pos
    change 0 < Real.pi * (τ : ℂ).im at hp
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] at *
    norm_num at *
    nlinarith
  have hpower (m : ℕ) : q ^ m =
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (τ : ℂ)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have harg : Complex.exp (2 * Real.pi * Complex.I *
      (((g : ℤ) : ℂ) * (25 * (τ : ℂ)) + (0 : ℤ)) / ((25 : ℕ) : ℂ)) = q ^ g := by
    rw [hpower]
    congr 1
    push_cast
    ring
  have haarg : Complex.exp (2 * Real.pi * Complex.I * (25 * (τ : ℂ))) = q ^ 25 := by
    rw [hpower]
    congr 1
    ring
  have hplus (n : ℕ) : (q ^ 25) ^ (n + 1) * q ^ g = q ^ (25 * (n + 1) + g) := by
    rw [← pow_mul, pow_add]
  have hminus (n : ℕ) : (q ^ 25) ^ (n + 1) * (q ^ g)⁻¹ =
      q ^ (25 * (n + 1) - g) := by
    rw [pow_sub₀ q hq0 (by omega), pow_mul]
  have hA := multipliable_residue_factors q hq (fun n => 25 * (n + 1) + g)
    (fun n => by omega)
  have hB := multipliable_residue_factors q hq (fun n => 25 * (n + 1) - g)
    (fun n => by omega)
  have hA0 := multipliable_residue_factors q hq (fun n => 25 * n + g)
    (fun n => by omega)
  have hshift : (1 - q ^ g) * (∏' n : ℕ, (1 - q ^ (25 * (n + 1) + g))) =
      ∏' n : ℕ, (1 - q ^ (25 * n + g)) := by
    simpa only [Nat.mul_zero, zero_add] using
      (tprod_eq_zero_mul' (f := fun n : ℕ => 1 - q ^ (25 * n + g)) hA).symm
  have hprod : (1 - q ^ g) *
      (∏' n : ℕ, ((1 - (q ^ 25) ^ (n + 1) * q ^ g) *
        (1 - (q ^ 25) ^ (n + 1) * (q ^ g)⁻¹))) =
      ∏' n : ℕ, ((1 - q ^ (25 * n + g)) * (1 - q ^ (25 * (n + 1) - g))) := by
    simp_rw [hplus, hminus]
    rw [hA.tprod_mul hB, ← mul_assoc, hshift, hA0.tprod_mul hB]
  unfold etaAnalytic25
  rw [ModularCurve.siegelFun_def, harg, haarg]
  push_cast
  simp only [mul_zero, zero_mul, zero_div, Complex.exp_zero, neg_one_mul, neg_mul, neg_neg, one_mul]
  rw [mul_assoc, hprod]

end N25
