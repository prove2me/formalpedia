-- Prove2me | solution 1 for MeasureTheory.Lp.coeFn_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:55:55.243828+00:00
-- url     : https://prove2.me/submissions/8f9176a7-2e26-4a01-acd3-c93ae4a67d5c

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
omit [NormedSpace ℝ E]
namespace Malliavin
namespace _root_.MeasureTheory.Lp
theorem _root_.solution {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {p : ℝ≥0∞} {ι : Type*} (s : Finset ι) (g : ι → Lp E p ν) :
    ⇑(∑ i ∈ s, g i) =ᵐ[ν] ∑ i ∈ s, ⇑(g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero (E := E) (p := p) (μ := ν)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (g a) (∑ i ∈ s, g i), ih] with t h1 h2
    rw [h1, Pi.add_apply, Pi.add_apply, h2]
end _root_.MeasureTheory.Lp
end Malliavin
