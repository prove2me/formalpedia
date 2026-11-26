-- Prove2me | solution 1 for Malliavin.symmetrizeL_comp_symmetrizeL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:35.40184+00:00
-- url     : https://prove2.me/submissions/c02a41ea-b88d-48ca-8076-f8a78714f9eb

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_symmetrizeL_symmetrizeL
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
theorem _root_.solution (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (symmetrizeL E (μ := μ) n p).comp (symmetrizeL E (μ := μ) n p) = symmetrizeL E (μ := μ) n p :=
  ContinuousLinearMap.ext fun f => symmetrizeL_symmetrizeL n p f
end Malliavin
