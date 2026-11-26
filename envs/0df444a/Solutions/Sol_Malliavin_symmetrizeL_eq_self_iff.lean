-- Prove2me | solution 1 for Malliavin.symmetrizeL_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:03.184826+00:00
-- url     : https://prove2.me/submissions/c967ec9f-1e9a-4f1e-86a0-44ceb1e94340

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_symmetrizeL_eq_self_of_ae_symmetric
import Theorems.Thm_Malliavin_ae_symmetric_of_symmetrizeL_eq_self

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
    symmetrizeL E (μ := μ) n p f = f ↔ ∀ σ : Equiv.Perm (Fin n),
      (⇑f ∘ fun t : Fin n → T => t ∘ σ) =ᵐ[Measure.pi fun _ : Fin n => μ] ⇑f :=
  ⟨ae_symmetric_of_symmetrizeL_eq_self n p f, symmetrizeL_eq_self_of_ae_symmetric n p f⟩
end Malliavin
