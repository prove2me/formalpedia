-- Prove2me | solution 1 for Malliavin.symmetrizeL_symmetrizeL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:09.167852+00:00
-- url     : https://prove2.me/submissions/b24d66f1-de28-4026-86ee-1fc216711b2f

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_symmetrize_symmetrize
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_symmetrize_congr_ae
import Theorems.Thm_Malliavin_coeFn_symmetrizeL
attribute [local simp] Malliavin.mem_symmetricSubmodule

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] (μ : Measure T) [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ}
namespace Malliavin
theorem _root_.solution (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp E p (Measure.pi fun _ : Fin n => μ)) :
    symmetrizeL E (μ := μ) n p (symmetrizeL E (μ := μ) n p f) = symmetrizeL E (μ := μ) n p f := by
  apply Lp.ext
  have h1 := coeFn_symmetrizeL n p (symmetrizeL E (μ := μ) n p f)
  have h2 := symmetrize_congr_ae (μ := μ) (coeFn_symmetrizeL n p f)
  rw [symmetrize_symmetrize] at h2
  exact h1.trans (h2.trans (coeFn_symmetrizeL n p f).symm)
end Malliavin
