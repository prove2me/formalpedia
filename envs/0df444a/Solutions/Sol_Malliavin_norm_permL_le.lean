-- Prove2me | solution 1 for Malliavin.norm_permL_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:55:55.883171+00:00
-- url     : https://prove2.me/submissions/11201754-d815-4990-9d7d-479718301ad1

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization

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
theorem _root_.solution (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (σ : Equiv.Perm (Fin n)) :
    ‖permL E (μ := μ) n p σ‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _
end Malliavin
