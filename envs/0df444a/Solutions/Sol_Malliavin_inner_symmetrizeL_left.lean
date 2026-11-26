-- Prove2me | solution 1 for Malliavin.inner_symmetrizeL_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:40.800078+00:00
-- url     : https://prove2.me/submissions/cf726d95-7640-4d73-8f23-650d58fcdcb5

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_symmetrizeL_apply
import Theorems.Thm_Malliavin_inner_permL_left
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
theorem _root_.solution (n : ℕ) (f g : Lp E 2 (Measure.pi fun _ : Fin n => μ)) :
    inner ℝ (symmetrizeL E (μ := μ) n 2 f) g = inner ℝ f (symmetrizeL E (μ := μ) n 2 g) := by
  simp only [symmetrizeL_apply, real_inner_smul_left, real_inner_smul_right, sum_inner, inner_sum]
  congr 1
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))
    (fun σ => inner ℝ f (permL E (μ := μ) n 2 σ g))]
  exact Finset.sum_congr rfl fun σ _ => inner_permL_left n σ f g
end Malliavin
