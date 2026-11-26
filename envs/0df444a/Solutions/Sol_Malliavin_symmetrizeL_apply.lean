-- Prove2me | solution 1 for Malliavin.symmetrizeL_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:48.446266+00:00
-- url     : https://prove2.me/submissions/dc0fc323-2870-4654-a994-fc67adcacab4

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
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
    symmetrizeL E (μ := μ) n p f =
      ((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), permL E (μ := μ) n p σ f := by
  simp only [symmetrizeL, smul_apply, _root_.sum_apply]
end Malliavin
