-- Prove2me | solution 1 for Malliavin.isSymmetric_symmetrize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:04.952736+00:00
-- url     : https://prove2.me/submissions/de8b1f1c-edc7-48e0-9e34-90e126d77696

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_symmetrize_comp_perm

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [AddCommGroup E] [Module ℝ E]
namespace Malliavin
theorem _root_.solution (n : ℕ) (f : (Fin n → T) → E) : IsSymmetric n (symmetrize n f) :=
  fun τ t => symmetrize_comp_perm n f τ t
end Malliavin
