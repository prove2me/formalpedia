-- Prove2me | solution 1 for Helfgott.symmetric_smoothing_derivative_l2_upper
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T21:11:32.772276+00:00
-- url     : https://prove2.me/submissions/11ff647b-b305-41f5-9c08-f5ff851931d1

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! An elementary upper bound for the derivative energy of the centered form
of Helfgott's symmetric smoothing (arXiv:1312.7748v2, (4.3), (4.5), (7.6)).
The paper's value is about 2.73753; the bound 17/5 derived here is sufficient
with the sharp polarization constant 1/2. Written by Codex. -/

open MeasureTheory
open scoped Interval

namespace Helfgott

lemma symmetric_smoothing_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => (1-s^2)^3 * Real.exp (-(s^2)/2))
      (-t * (1-t^2)^2 * (7-t^2) * Real.exp (-(t^2)/2)) t := by
  convert! (((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2)).pow 3).mul
    ((((hasDerivAt_id t).pow 2).neg.div_const 2).exp) using 1 <;> simp <;> ring

theorem symmetric_smoothing_derivative_l2_upper :
    (∫ t in (-1 : ℝ)..1,
      (-t * (1-t^2)^2 * (7-t^2) * Real.exp (-(t^2)/2))^2) ≤ (17/5 : ℝ) := by
  let P : ℝ → ℝ := fun t => t^2 * (1-t^2)^4 * (7-t^2)^2
  have hpoint (t : ℝ) :
      (-t * (1-t^2)^2 * (7-t^2) * Real.exp (-(t^2)/2))^2 ≤ P t := by
    have hexp : Real.exp (-(t^2)/2)^2 = Real.exp (-(t^2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have he : Real.exp (-(t^2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg t]
    have h := mul_le_mul_of_nonneg_left he (show 0 ≤ P t by dsimp [P]; positivity)
    convert! h using 1 <;> dsimp [P] <;> simp only [mul_pow, pow_mul, neg_sq, hexp, mul_one] <;> ring
  let Q : ℝ → ℝ := fun t => (49 / 1 : ℝ) * t ^ 3 / 3 + (-210 / 1 : ℝ) * t ^ 5 / 5 + (351 / 1 : ℝ) * t ^ 7 / 7 + (-284 / 1 : ℝ) * t ^ 9 / 9 + (111 / 1 : ℝ) * t ^ 11 / 11 + (-18 / 1 : ℝ) * t ^ 13 / 13 + (1 / 1 : ℝ) * t ^ 15 / 15
  have hQ (t : ℝ) : HasDerivAt Q (P t) t := by
    dsimp [Q,P]
    convert! ((((((((hasDerivAt_const t (0 : ℝ)).add ((((hasDerivAt_id t).pow 3).const_mul (49 / 1 : ℝ)).div_const 3)).add ((((hasDerivAt_id t).pow 5).const_mul (-210 / 1 : ℝ)).div_const 5)).add ((((hasDerivAt_id t).pow 7).const_mul (351 / 1 : ℝ)).div_const 7)).add ((((hasDerivAt_id t).pow 9).const_mul (-284 / 1 : ℝ)).div_const 9)).add ((((hasDerivAt_id t).pow 11).const_mul (111 / 1 : ℝ)).div_const 11)).add ((((hasDerivAt_id t).pow 13).const_mul (-18 / 1 : ℝ)).div_const 13)).add ((((hasDerivAt_id t).pow 15).const_mul (1 / 1 : ℝ)).div_const 15)) using 1
    all_goals try funext x
    all_goals simp
    all_goals ring
  have hpint : (∫ t in (-1 : ℝ)..1, P t) = 152576 / 45045 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hQ t)
      ((by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _)]
    norm_num [Q]
  have hmono : (∫ t in (-1 : ℝ)..1,
      (-t * (1-t^2)^2 * (7-t^2) * Real.exp (-(t^2)/2))^2) ≤
      ∫ t in (-1 : ℝ)..1, P t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (by fun_prop : Continuous (fun t : ℝ =>
        (-t * (1-t^2)^2 * (7-t^2) * Real.exp (-(t^2)/2))^2)).intervalIntegrable _ _
    · exact (by dsimp [P]; fun_prop : Continuous P).intervalIntegrable _ _
    · intro t _; exact hpoint t
  rw [hpint] at hmono
  exact le_trans hmono (by norm_num)

end Helfgott

theorem solution :
    (∫ t in (-1 : ℝ)..1,
      (-t * (1-t^2)^2 * (7-t^2) * Real.exp (-(t^2)/2))^2) ≤ (17/5 : ℝ) :=
  Helfgott.symmetric_smoothing_derivative_l2_upper

#print axioms solution
