-- Prove2me | solution 1 for Malliavin.symmetrizeL_eq_self_of_ae_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:12.136265+00:00
-- url     : https://prove2.me/submissions/7157ac17-6755-46f1-8588-048bc5541e19

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_symmetrize_apply_of_forall
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
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
    (f : Lp E p (Measure.pi fun _ : Fin n => μ))
    (hf : ∀ σ : Equiv.Perm (Fin n),
      (⇑f ∘ fun t : Fin n → T => t ∘ σ) =ᵐ[Measure.pi fun _ : Fin n => μ] ⇑f) :
    symmetrizeL E (μ := μ) n p f = f := by
  apply Lp.ext
  refine (coeFn_symmetrizeL n p f).trans ?_
  filter_upwards [Filter.eventually_all.2 hf] with t ht
  exact symmetrize_apply_of_forall fun σ => ht σ
end Malliavin
