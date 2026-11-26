-- Prove2me | solution 1 for Malliavin.aestronglyMeasurable_symmetrize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:14.684366+00:00
-- url     : https://prove2.me/submissions/f64ee5b6-a2b8-40f2-a0d6-23528066f5df

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_symmetrize_eq_smul_sum
import Theorems.Thm_Malliavin_aestronglyMeasurable_comp_perm

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
theorem _root_.solution {n : ℕ} {f : (Fin n → T) → E}
    (hf : AEStronglyMeasurable f (Measure.pi fun _ : Fin n => μ)) :
    AEStronglyMeasurable (symmetrize n f) (Measure.pi fun _ : Fin n => μ) := by
  rw [symmetrize_eq_smul_sum]
  refine AEStronglyMeasurable.const_smul ?_ _
  exact Finset.sum_induction _ (fun g => AEStronglyMeasurable g (Measure.pi fun _ : Fin n => μ))
    (fun _ _ hg hg' => hg.add hg') aestronglyMeasurable_const
    fun σ _ => aestronglyMeasurable_comp_perm hf σ
end Malliavin
