-- Prove2me | solution 1 for Malliavin.isSymmetric_iff_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:42.766197+00:00
-- url     : https://prove2.me/submissions/920e597a-8e7b-4dcb-94aa-3bb7de90694d

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_isSymmetric_of_swap

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
namespace Malliavin
theorem _root_.solution {n : ℕ} {f : (Fin n → T) → E} :
    IsSymmetric n f ↔ ∀ x y : Fin n, x ≠ y → ∀ t : Fin n → T, f (t ∘ Equiv.swap x y) = f t :=
  ⟨fun hf _ _ _ t => hf _ t, isSymmetric_of_swap⟩
end Malliavin
