-- Prove2me | solution 1 for Malliavin.norm_sq_eq_norm_sq_symmetrizeL_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:39.434416+00:00
-- url     : https://prove2.me/submissions/96088823-3f22-426b-879f-7b80fae9ed14

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_inner_symmetrizeL_sub_symmetrizeL
attribute [local simp] Malliavin.mem_symmetricSubmodule

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] {μ : Measure T} [SigmaFinite μ]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace Malliavin
theorem _root_.solution (n : ℕ)
    (f : Lp E 2 (Measure.pi fun _ : Fin n => μ)) :
    ‖f‖ ^ 2 = ‖symmetrizeL E (μ := μ) n 2 f‖ ^ 2 + ‖f - symmetrizeL E (μ := μ) n 2 f‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (symmetrizeL E (μ := μ) n 2 f)
    (f - symmetrizeL E (μ := μ) n 2 f) (inner_symmetrizeL_sub_symmetrizeL n f)
  rw [add_sub_cancel] at h
  simpa only [sq] using h
end Malliavin
