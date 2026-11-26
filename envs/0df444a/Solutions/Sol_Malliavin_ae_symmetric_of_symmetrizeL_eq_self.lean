-- Prove2me | solution 1 for Malliavin.ae_symmetric_of_symmetrizeL_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:13.060799+00:00
-- url     : https://prove2.me/submissions/7acb6de4-d71e-48dc-96ea-e8f2da455755

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_symmetrize_comp_perm
import Theorems.Thm_Malliavin_coeFn_symmetrizeL

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
    (f : Lp E p (Measure.pi fun _ : Fin n => μ)) (hf : symmetrizeL E (μ := μ) n p f = f)
    (σ : Equiv.Perm (Fin n)) :
    (⇑f ∘ fun t : Fin n → T => t ∘ σ) =ᵐ[Measure.pi fun _ : Fin n => μ] ⇑f := by
  have h1 : ⇑f =ᵐ[Measure.pi fun _ : Fin n => μ] symmetrize n ⇑f := by
    have := coeFn_symmetrizeL (E := E) (μ := μ) n p f
    rwa [hf] at this
  have h2 : (⇑f ∘ fun t : Fin n → T => t ∘ σ) =ᵐ[Measure.pi fun _ : Fin n => μ]
      (symmetrize n ⇑f ∘ fun t : Fin n → T => t ∘ σ) :=
    (measurePreserving_comp_perm μ n σ).quasiMeasurePreserving.ae_eq_comp h1
  have h3 : (symmetrize n ⇑f ∘ fun t : Fin n → T => t ∘ σ) = symmetrize n ⇑f :=
    funext fun t => symmetrize_comp_perm n ⇑f σ t
  rw [h3] at h2
  exact h2.trans h1.symm
end Malliavin
