-- Prove2me | solution 1 for Kyprianou.Ch03.examples_singleLog
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:04:02.739211+00:00
-- url     : https://prove2.me/submissions/fdd5c05a-2be9-4ac0-9839-fe3ffffd1123

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace SlogAux

lemma key (a b : ℝ) (ha : Real.exp 1 ≤ a) (hb : Real.exp 1 ≤ b) :
    Real.log (max (a + b) (Real.exp 1)) ≤ 2 * Real.log a * Real.log b := by
  have ha1 : 1 ≤ Real.log a := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) ha
  have hb1 : 1 ≤ Real.log b := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hb
  have hapos : 0 < a := lt_of_lt_of_le (Real.exp_pos 1) ha
  have hbpos : 0 < b := lt_of_lt_of_le (Real.exp_pos 1) hb
  have hmax : max (a + b) (Real.exp 1) = a + b := by
    apply max_eq_left; linarith
  rw [hmax]
  -- a + b ≤ 2 * max a b ≤ a * b, log(a+b) ≤ log a + log b ≤ 2 log a log b
  have e2 : (2:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ); linarith
  have hab : a + b ≤ a * b := by nlinarith
  have h1 : Real.log (a + b) ≤ Real.log a + Real.log b := by
    rw [← Real.log_mul hapos.ne' hbpos.ne']
    exact Real.log_le_log (by linarith) hab
  nlinarith

end SlogAux

open Kyprianou.Ch03 in
theorem solution :
    IsSubmultiplicative (fun x : ℝ =>
       Real.log (max |x| (Real.exp 1))) := by
  refine ⟨fun x => Real.log_nonneg ?_, 2, by norm_num, fun x y => ?_⟩
  · have := Real.add_one_le_exp (1:ℝ)
    exact le_trans (by linarith) (le_max_right _ _)
  · set a := max |x| (Real.exp 1)
    set b := max |y| (Real.exp 1)
    have ha : Real.exp 1 ≤ a := le_max_right _ _
    have hb : Real.exp 1 ≤ b := le_max_right _ _
    have hxy : |x + y| ≤ a + b :=
      (abs_add_le x y).trans (add_le_add (le_max_left _ _) (le_max_left _ _))
    have hmono : Real.log (max |x + y| (Real.exp 1)) ≤ Real.log (max (a + b) (Real.exp 1)) := by
      apply Real.log_le_log (lt_of_lt_of_le (Real.exp_pos 1) (le_max_right _ _))
      exact max_le_max hxy le_rfl
    exact hmono.trans (SlogAux.key a b ha hb)
