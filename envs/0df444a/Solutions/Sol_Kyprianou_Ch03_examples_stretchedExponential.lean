-- Prove2me | solution 1 for Kyprianou.Ch03.examples_stretchedExponential
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:04:06.097827+00:00
-- url     : https://prove2.me/submissions/1d249bc7-d900-4b58-8b1b-3864c6368f23

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03 in
theorem solution :
    (∀ beta : ℝ, 0 < beta → beta ≤ 1 →
       IsSubmultiplicative (fun x : ℝ => Real.exp (|x| ^ beta))) := by
  intro beta hb0 hb1
  refine ⟨fun x => (Real.exp_pos _).le, 1, one_pos, fun x y => ?_⟩
  rw [one_mul, ← Real.exp_add]
  apply Real.exp_le_exp.2
  calc |x + y| ^ beta ≤ (|x| + |y|) ^ beta :=
        Real.rpow_le_rpow (abs_nonneg _) (abs_add_le x y) hb0.le
    _ ≤ |x| ^ beta + |y| ^ beta :=
        Real.rpow_add_le_add_rpow (abs_nonneg _) (abs_nonneg _) hb0.le hb1
