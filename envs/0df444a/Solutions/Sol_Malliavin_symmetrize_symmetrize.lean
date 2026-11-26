-- Prove2me | solution 1 for Malliavin.symmetrize_symmetrize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:54.703231+00:00
-- url     : https://prove2.me/submissions/8c1b96a1-644a-49e8-b748-0134d8670790

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_isSymmetric_symmetrize
import Theorems.Thm_Malliavin_symmetrize_of_isSymmetric

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [AddCommGroup E] [Module ℝ E]
namespace Malliavin
theorem _root_.solution (n : ℕ) (f : (Fin n → T) → E) :
    symmetrize n (symmetrize n f) = symmetrize n f :=
  symmetrize_of_isSymmetric (isSymmetric_symmetrize n f)
end Malliavin
