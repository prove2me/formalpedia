-- Prove2me | solution 1 for Malliavin.symmetrize_of_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:06.907722+00:00
-- url     : https://prove2.me/submissions/e7f9ac2a-cb9e-4d82-ab21-2443e3729bfd

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_symmetrize_apply_of_forall

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [AddCommGroup E] [Module ℝ E]
namespace Malliavin
theorem _root_.solution {n : ℕ} {f : (Fin n → T) → E} (hf : IsSymmetric n f) :
    symmetrize n f = f :=
  funext fun t => symmetrize_apply_of_forall fun σ => hf σ t
end Malliavin
