-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_sextic_moment_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T17:16:18.56894+00:00
-- url     : https://prove2.me/submissions/dbc02198-3da8-4602-9247-1da4ac46fea3

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

open MeasureTheory Real

private noncomputable def weightedMono (s : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  x^n * exp (-(x^2 + (s*(x^3-3*x))^2)/2)

private theorem weightedMono_integrable (s : ℝ) (n : ℕ) : Integrable (weightedMono s n) := by
  have hg : Integrable fun x : ℝ => x^n * exp (-(1/2 : ℝ) * x^2) := by
    simpa only [rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq (by norm_num : 0 < (1/2:ℝ))
      (lt_of_lt_of_le (by norm_num : (-1:ℝ) < 0) (Nat.cast_nonneg n))
  apply hg.mono (by unfold weightedMono; fun_prop)
  filter_upwards with x
  simp only [weightedMono, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply Real.exp_le_exp.mpr
  linarith only [sq_nonneg (s*(x^3-3*x))]

theorem solution (s : ℝ) (n : ℕ) :
    let M (k : ℕ) := ∫ x : ℝ, x^k * Real.exp (-(x^2+(s*(x^3-3*x))^2)/2)
    3*s^2*M (n+6) = ((n:ℝ)+1)*M n - (1+9*s^2)*M (n+2) + 12*s^2*M (n+4) := by
  let f := weightedMono s
  let A : ℝ := n+1
  let B : ℝ := 1+9*s^2
  let C : ℝ := 12*s^2
  let D : ℝ := 3*s^2
  let derivF (x : ℝ) := A*f n x - B*f (n+2) x + C*f (n+4) x - D*f (n+6) x
  have hdiff (x : ℝ) : HasDerivAt (f (n+1)) (derivF x) x := by
    have hp := ((hasDerivAt_pow 3 x).sub (hasDerivAt_const_mul (x := x) 3)).const_mul s
    have he := (((((hasDerivAt_pow 2 x).add (hp.pow 2)).neg).div_const 2).exp)
    apply ((hasDerivAt_pow (n+1) x).mul he).congr_deriv
    dsimp [derivF,f,weightedMono,A,B,C,D]
    push_cast
    simp only [pow_add, pow_one, Nat.add_sub_cancel, Nat.reduceSub, Nat.cast_ofNat]
    ring
  have hint (n : ℕ) : Integrable (f n) := weightedMono_integrable s n
  have hdint : Integrable derivF :=
    ((((hint n).const_mul A).sub ((hint (n+2)).const_mul B)).add
      ((hint (n+4)).const_mul C)).sub ((hint (n+6)).const_mul D)
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hdiff hdint (hint (n+1))
  change (∫ x : ℝ, (A*f n x - B*f (n+2) x + C*f (n+4) x) - D*f (n+6) x) = 0 at hz
  have hab : Integrable (fun x => A*f n x-B*f (n+2) x) :=
    ((hint n).const_mul A).sub ((hint (n+2)).const_mul B)
  have habc : Integrable (fun x => A*f n x-B*f (n+2) x+C*f (n+4) x) :=
    hab.add ((hint (n+4)).const_mul C)
  rw [integral_sub habc ((hint (n+6)).const_mul D),
      integral_add hab ((hint (n+4)).const_mul C),
      integral_sub ((hint n).const_mul A) ((hint (n+2)).const_mul B)] at hz
  simp only [integral_const_mul] at hz
  change D*(∫ x, f (n+6) x) = A*(∫ x, f n x)- B*(∫ x, f (n+2) x) + C*(∫ x, f (n+4) x)
  linarith only [hz]
