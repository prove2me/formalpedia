-- Prove2me | solution 1 for Malliavin.symmetrize_apply_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:29.271825+00:00
-- url     : https://prove2.me/submissions/4628d214-8b4f-47d1-b480-caa4c7da09bf

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
theorem _root_.solution {n : ℕ} {f : (Fin n → T) → E} {t : Fin n → T}
    (h : ∀ σ : Equiv.Perm (Fin n), f (t ∘ σ) = f t) : symmetrize n f t = f t := by
  rw [symmetrize_apply, Finset.sum_congr rfl (fun σ _ => h σ), Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_smul]
end Malliavin
