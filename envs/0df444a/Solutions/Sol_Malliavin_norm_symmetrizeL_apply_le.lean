-- Prove2me | solution 1 for Malliavin.norm_symmetrizeL_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:19.729722+00:00
-- url     : https://prove2.me/submissions/c5a76fb7-76bd-4a69-baac-093d9bad6169

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_norm_symmetrizeL_le
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
    ‖symmetrizeL E (μ := μ) n p f‖ ≤ ‖f‖ := by
  have h := (symmetrizeL E (μ := μ) n p).le_of_opNorm_le
    (norm_symmetrizeL_le (E := E) (μ := μ) n p) f
  simpa only [one_mul] using h
end Malliavin
