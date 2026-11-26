-- Prove2me | solution 1 for Malliavin.inner_symmetrizeL_sub_symmetrizeL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:45.718085+00:00
-- url     : https://prove2.me/submissions/0ddb7f6d-e91f-4a02-be60-6fffe7c63210

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_symmetrizeL_symmetrizeL
import Theorems.Thm_Malliavin_inner_symmetrizeL_left

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] {μ : Measure T} [SigmaFinite μ]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace Malliavin
theorem _root_.solution (n : ℕ) (f : Lp E 2 (Measure.pi fun _ : Fin n => μ)) :
    inner ℝ (symmetrizeL E (μ := μ) n 2 f) (f - symmetrizeL E (μ := μ) n 2 f) = 0 := by
  rw [inner_sub_right, inner_symmetrizeL_left n f (symmetrizeL E (μ := μ) n 2 f),
    symmetrizeL_symmetrizeL, inner_symmetrizeL_left, sub_self]
end Malliavin
