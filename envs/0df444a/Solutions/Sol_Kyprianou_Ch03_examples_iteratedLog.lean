-- Prove2me | solution 1 for Kyprianou.Ch03.examples_iteratedLog
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:04:04.60895+00:00
-- url     : https://prove2.me/submissions/1efddb80-8490-414e-8dd5-3062dfae03d3

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace IlogAux

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

end IlogAux

open Kyprianou.Ch03 in
theorem solution :
    IsSubmultiplicative (fun x : ℝ =>
       Real.log (Real.log (max |x| (Real.exp (Real.exp 1))))) := by
  have hee : Real.exp 1 ≤ Real.exp (Real.exp 1) :=
    Real.exp_le_exp.2 (by have := Real.add_one_le_exp (1:ℝ); linarith)
  have hlogge : ∀ z : ℝ, Real.exp (Real.exp 1) ≤ z → Real.exp 1 ≤ Real.log z := by
    intro z hz
    rw [← Real.log_exp (Real.exp 1)]
    exact Real.log_le_log (Real.exp_pos _) hz
  refine ⟨fun x => Real.log_nonneg ?_, 2, by norm_num, fun x y => ?_⟩
  · have h1 := hlogge _ (le_max_right |x| (Real.exp (Real.exp 1)))
    have := Real.add_one_le_exp (1:ℝ); linarith
  · set a := max |x| (Real.exp (Real.exp 1))
    set b := max |y| (Real.exp (Real.exp 1))
    have ha : Real.exp (Real.exp 1) ≤ a := le_max_right _ _
    have hb : Real.exp (Real.exp 1) ≤ b := le_max_right _ _
    have hA := hlogge a ha
    have hB := hlogge b hb
    have hapos : 0 < a := lt_of_lt_of_le (Real.exp_pos _) ha
    have hbpos : 0 < b := lt_of_lt_of_le (Real.exp_pos _) hb
    have e2 : (2:ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1:ℝ); linarith
    have hxy : |x + y| ≤ a + b :=
      (abs_add_le x y).trans (add_le_add (le_max_left _ _) (le_max_left _ _))
    have hm : max |x + y| (Real.exp (Real.exp 1)) ≤ a + b :=
      max_le hxy (by linarith)
    have hmpos : 0 < max |x + y| (Real.exp (Real.exp 1)) :=
      lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
    have hab : a + b ≤ a * b := by nlinarith
    have h1 : Real.log (max |x + y| (Real.exp (Real.exp 1))) ≤ Real.log a + Real.log b := by
      rw [← Real.log_mul hapos.ne' hbpos.ne']
      exact Real.log_le_log hmpos (hm.trans hab)
    have hLpos : 0 < Real.log (max |x + y| (Real.exp (Real.exp 1))) := by
      have := hlogge _ (le_max_right |x + y| (Real.exp (Real.exp 1)))
      linarith [Real.exp_pos 1]
    have h2 : Real.log (Real.log (max |x + y| (Real.exp (Real.exp 1)))) ≤
        Real.log (max (Real.log a + Real.log b) (Real.exp 1)) :=
      Real.log_le_log hLpos (h1.trans (le_max_left _ _))
    exact h2.trans (IlogAux.key _ _ hA hB)
