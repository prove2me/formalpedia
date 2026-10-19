-- Prove2me | solution 1 for OAI.C0Absorption.finiteInverse_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:43:43.180203+00:00
-- url     : https://prove2.me/submissions/9f9c3cb6-a5f8-4125-a6eb-87073d617ea6

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations
import Definitions.Def_OAI_Analysis_C0Absorption_Detection
import Definitions.Def_OAI_Analysis_C0Absorption_Grid
import Definitions.Def_OAI_Analysis_C0Absorption_Weights
import Definitions.Def_OAI_Analysis_C0Absorption_Angles
import Definitions.Def_OAI_Analysis_C0Absorption_Blocks
import Definitions.Def_OAI_Analysis_C0Absorption_Correction
import Definitions.Def_OAI_Analysis_C0Absorption_Frozen
import Definitions.Def_OAI_Analysis_C0Absorption_Tags
import Definitions.Def_OAI_Analysis_C0Absorption_Operators
import Definitions.Def_OAI_Analysis_C0Absorption_Shift
import Definitions.Def_OAI_Analysis_C0Absorption_Space
import Definitions.Def_OAI_Analysis_C0Absorption_Finite

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty
variable {N : ℕ}


theorem solution (W : FrozenWeights) (y : FInput N) : ‖finiteInverseFunction W y‖≤5*‖y‖ := by
  have hy := norm_nonneg y
  have hnext : ∀ l : FLevel N, |finiteNext W l y| ≤ 2 * ‖y‖ := by
    intro l
    unfold finiteNext
    split_ifs
    · exact finiteRow_bound W _ y
    · have := norm_le_pi_norm y (.inl l.1)
      rw [Real.norm_eq_abs] at this; linarith
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) hy)).mpr
  rintro (i | ⟨l, b⟩)
  · rw [finiteInverse_row, Real.norm_eq_abs]
    exact (finiteRow_bound W _ y).trans (by linarith)
  · rw [finiteInverse_block, Real.norm_eq_abs]
    have h1 := norm_le_pi_norm y (.inr ⟨l, b⟩)
    rw [Real.norm_eq_abs] at h1
    have h2 := W.vector_bound (l.1.val, l.2.val) b
    have h3 := finiteRow_bound W l y
    have h4 := hnext l
    have h5 : |W.vector (l.1.val, l.2.val) b * (finiteRow W l y - finiteNext W l y)| ≤ 4 * ‖y‖ := by
      rw [abs_mul]
      have : |finiteRow W l y - finiteNext W l y| ≤ 4 * ‖y‖ :=
        (abs_sub _ _).trans (by linarith)
      calc |W.vector (l.1.val, l.2.val) b| * |finiteRow W l y - finiteNext W l y|
          ≤ 1 * (4 * ‖y‖) := mul_le_mul h2 this (abs_nonneg _) zero_le_one
        _ = 4 * ‖y‖ := one_mul _
    calc |y (.inr ⟨l, b⟩) - W.vector (l.1.val, l.2.val) b * (finiteRow W l y - finiteNext W l y)|
        ≤ |y (.inr ⟨l, b⟩)| + |W.vector (l.1.val, l.2.val) b * (finiteRow W l y - finiteNext W l y)| :=
          abs_sub _ _
      _ ≤ 5 * ‖y‖ := by linarith

