-- Prove2me | solution 1 for Malliavin.coeFn_permL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:40.573838+00:00
-- url     : https://prove2.me/submissions/d82dbd99-4df9-4044-9aee-0ef449084d98

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
theorem _root_.solution (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (σ : Equiv.Perm (Fin n))
    (f : Lp E p (Measure.pi fun _ : Fin n => μ)) :
    ⇑(permL E (μ := μ) n p σ f) =ᵐ[Measure.pi fun _ : Fin n => μ]
      ⇑f ∘ fun t : Fin n → T => t ∘ σ :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_comp_perm μ n σ)
end Malliavin
