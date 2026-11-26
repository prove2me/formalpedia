-- Prove2me | solution 1 for Malliavin.symmetrize_comp_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:28.715076+00:00
-- url     : https://prove2.me/submissions/4f949df6-4b29-418a-9155-c93bed234ac5

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
theorem _root_.solution (n : ℕ) (f : (Fin n → T) → E) (τ : Equiv.Perm (Fin n))
    (t : Fin n → T) : symmetrize n f (t ∘ τ) = symmetrize n f t := by
  simp only [symmetrize_apply]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ : Equiv.Perm (Fin n) => f (t ∘ σ))
end Malliavin
