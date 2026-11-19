-- Prove2me | solution 1 for Kyprianou.Ch03.exercise33SubmultiplicativeExamples
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:12:12.994193+00:00
-- url     : https://prove2.me/submissions/9f38f443-0102-4ccb-90f5-48850ccad8b3

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
import Theorems.Thm_Kyprianou_Ch03_examples_positiveMax
import Theorems.Thm_Kyprianou_Ch03_examples_positiveMaxPower
import Theorems.Thm_Kyprianou_Ch03_examples_absoluteMax
import Theorems.Thm_Kyprianou_Ch03_examples_absoluteMaxPower
import Theorems.Thm_Kyprianou_Ch03_examples_stretchedExponential
import Theorems.Thm_Kyprianou_Ch03_examples_singleLog
import Theorems.Thm_Kyprianou_Ch03_examples_iteratedLog
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03


theorem solution :
IsSubmultiplicative (fun x : ℝ => max x 1) ∧
    (∀ alpha : ℝ, 0 < alpha →
       IsSubmultiplicative (fun x : ℝ => (max x 1) ^ alpha)) ∧
    IsSubmultiplicative (fun x : ℝ => max |x| 1) ∧
    (∀ alpha : ℝ, 0 < alpha →
       IsSubmultiplicative (fun x : ℝ => (max |x| 1) ^ alpha)) ∧
    (∀ beta : ℝ, 0 < beta → beta ≤ 1 →
       IsSubmultiplicative (fun x : ℝ => Real.exp (|x| ^ beta))) ∧
    IsSubmultiplicative (fun x : ℝ =>
       Real.log (max |x| (Real.exp 1))) ∧
    IsSubmultiplicative (fun x : ℝ =>
       Real.log (Real.log (max |x| (Real.exp (Real.exp 1))))) := by
  exact ⟨
    Kyprianou.Ch03.examples_positiveMax,
    Kyprianou.Ch03.examples_positiveMaxPower,
    Kyprianou.Ch03.examples_absoluteMax,
    Kyprianou.Ch03.examples_absoluteMaxPower,
    Kyprianou.Ch03.examples_stretchedExponential,
    Kyprianou.Ch03.examples_singleLog,
    Kyprianou.Ch03.examples_iteratedLog
  ⟩

