-- Prove2me | solution 1 for Malliavin.symmetrize_eq_smul_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:43:47.435846+00:00
-- url     : https://prove2.me/submissions/5443a0f4-56b4-4862-921e-0dd802aa7b91

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [AddCommGroup E] [Module ℝ E]
namespace Malliavin
theorem _root_.solution (n : ℕ) (f : (Fin n → T) → E) :
    symmetrize n f =
      ((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), f ∘ (fun t : Fin n → T => t ∘ σ) := by
  ext t
  simp only [symmetrize_apply, Pi.smul_apply, Finset.sum_apply, Function.comp_apply]
end Malliavin
