-- Prove2me | solution 1 for Malliavin.coeFn_symmetrizeL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:33.426855+00:00
-- url     : https://prove2.me/submissions/99d2765f-3573-4742-a7fc-2c007ed36e2d

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_MeasureTheory_Lp_coeFn_finset_sum
import Theorems.Thm_Malliavin_coeFn_permL
import Theorems.Thm_Malliavin_symmetrizeL_apply

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
    ⇑(symmetrizeL E (μ := μ) n p f) =ᵐ[Measure.pi fun _ : Fin n => μ] symmetrize n ⇑f := by
  rw [symmetrizeL_apply]
  filter_upwards [Lp.coeFn_smul ((n.factorial : ℝ)⁻¹)
      (∑ σ : Equiv.Perm (Fin n), permL E (μ := μ) n p σ f),
    Lp.coeFn_finset_sum Finset.univ (fun σ : Equiv.Perm (Fin n) => permL E (μ := μ) n p σ f),
    Filter.eventually_all.2 (fun σ => coeFn_permL (E := E) (μ := μ) n p σ f)] with t h1t h2t h3t
  rw [h1t, Pi.smul_apply, h2t, Finset.sum_apply, symmetrize_apply]
  congr 1
  exact Finset.sum_congr rfl fun σ _ => h3t σ
end Malliavin
