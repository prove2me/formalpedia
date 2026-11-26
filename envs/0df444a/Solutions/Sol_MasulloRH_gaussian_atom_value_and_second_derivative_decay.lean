-- Prove2me | solution 1 for MasulloRH.gaussian_atom_value_and_second_derivative_decay
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T13:29:21.210226+00:00
-- url     : https://prove2.me/submissions/42a5967f-06dc-4d10-aa50-77438f46db2f

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem solution (C r b z : ℝ) (hr : |r| ≤ 1) (hb : |b| ≤ 2)
    (hu : 28 ≤ C * Real.exp (b*z)) (hz : 8*(r*z) ≤ C * Real.exp (b*z)) :
    let f := fun x : ℝ => Real.exp (r*x - C*Real.exp (b*x))
    |f z| ≤ 1/(27/10:ℝ)^24 ∧ |deriv (deriv f) z| ≤ 161/(27/10:ℝ)^17 := by
  let v (x : ℝ) := C * Real.exp (b*x)
  let f (x : ℝ) := Real.exp (r*x - v x)
  change |f z| ≤ _ ∧ |deriv (deriv f) z| ≤ _
  have dv (x : ℝ) : HasDerivAt v (b*v x) x := by
    have h := (((hasDerivAt_id x).const_mul b).exp).const_mul C
    change HasDerivAt (fun y => C*Real.exp (b*y)) (b*v x) x
    simpa only [v, id_eq, mul_one, mul_left_comm, mul_comm, mul_assoc] using h
  have df (x : ℝ) : HasDerivAt f ((r-b*v x)*f x) x := by
    have h := (((hasDerivAt_id x).const_mul r).sub (dv x)).exp
    change HasDerivAt (fun y => Real.exp (r*y-v y)) ((r-b*v x)*f x) x
    simpa only [f, id_eq, Pi.sub_apply, mul_one, mul_comm] using h
  have ddf : deriv (deriv f) z = ((r-b*v z)^2-b^2*v z)*f z := by
    rw [show deriv f = fun x => (r-b*v x)*f x from funext fun x => (df x).deriv]
    have h := (((dv z).const_mul b).const_sub r).mul (df z)
    calc
      _ = -(b*(b*v z))*f z + (r-b*v z)*((r-b*v z)*f z) := h.deriv
      _ = _ := by ring
  change 28 ≤ v z at hu
  change 8*(r*z) ≤ v z at hz
  have hnon : 0 ≤ v z := by linarith
  have expN (n : ℕ) : (27/10:ℝ)^n ≤ Real.exp (n:ℝ) := by
    have he : (27/10:ℝ) ≤ Real.exp 1 := (by norm_num : (27/10:ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le
    simpa using (pow_le_pow_left₀ (by norm_num) he n).trans_eq (Real.exp_nat_mul 1 n).symm
  have neg (n : ℕ) {w : ℝ} (hw : w ≤ -(n:ℝ)) : Real.exp w ≤ 1/(27/10:ℝ)^n := by
    apply (Real.exp_le_exp.mpr hw).trans
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) (expN n)
  have hf : 0 < f z := Real.exp_pos _
  constructor
  · rw [abs_of_pos hf]
    exact neg 24 (by norm_num; linarith)
  · have hvb : |b*v z| ≤ 2*v z := by
      rw [abs_mul,abs_of_nonneg hnon]
      exact mul_le_mul_of_nonneg_right hb hnon
    have hlin : |r-b*v z| ≤ 1+2*v z :=
      (abs_sub _ _).trans (add_le_add hr hvb)
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hlin 2
    rw [sq_abs] at hsq
    have hb2 := pow_le_pow_left₀ (abs_nonneg b) hb 2
    rw [sq_abs] at hb2
    have hmul := mul_le_mul_of_nonneg_right hb2 hnon
    have hp : |(r-b*v z)^2-b^2*v z| ≤ 161*Real.exp (v z/4) := by
      apply (abs_sub _ _).trans
      rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg (mul_nonneg (sq_nonneg _) hnon)]
      have h0 := Real.add_one_le_exp (v z/4)
      have h2 := Real.pow_div_factorial_le_exp (v z/4) (show 0 ≤ v z/4 by linarith) 2
      norm_num [Nat.factorial] at h2
      nlinarith
    rw [ddf, abs_mul, abs_of_pos hf]
    calc
      _ ≤ (161*Real.exp (v z/4))*f z := mul_le_mul_of_nonneg_right hp hf.le
      _ = 161*Real.exp (r*z-3*(v z)/4) := by
        dsimp [f]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ 161*(1/(27/10:ℝ)^17) := mul_le_mul_of_nonneg_left (neg 17 (by norm_num; linarith)) (by norm_num)
      _ = _ := by ring
