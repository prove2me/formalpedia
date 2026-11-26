-- Prove2me | solution 1 for Malliavin.isSymmetric_of_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:54:54.097439+00:00
-- url     : https://prove2.me/submissions/20f58b8a-dac7-4db5-9c14-18dc722aa1b7

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
namespace Malliavin
theorem _root_.solution {n : ℕ} {f : (Fin n → T) → E}
    (h : ∀ x y : Fin n, x ≠ y → ∀ t : Fin n → T, f (t ∘ Equiv.swap x y) = f t) :
    IsSymmetric n f := by
  intro σ
  induction σ using Equiv.Perm.swap_induction_on with
  | one => intro t; rfl
  | swap_mul τ x y hxy ih =>
    intro t
    calc f (t ∘ ⇑(Equiv.swap x y * τ)) = f ((t ∘ Equiv.swap x y) ∘ τ) := rfl
      _ = f (t ∘ Equiv.swap x y) := ih _
      _ = f t := h x y hxy t
end Malliavin
