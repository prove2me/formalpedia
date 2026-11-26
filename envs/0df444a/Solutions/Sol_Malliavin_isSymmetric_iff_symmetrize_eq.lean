-- Prove2me | solution 1 for Malliavin.isSymmetric_iff_symmetrize_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:46.209989+00:00
-- url     : https://prove2.me/submissions/0340e2d6-f30a-435c-89fd-6825471074f4

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
theorem _root_.solution {n : ℕ} {f : (Fin n → T) → E} :
    IsSymmetric n f ↔ symmetrize n f = f :=
  ⟨symmetrize_of_isSymmetric, fun h => h ▸ isSymmetric_symmetrize n f⟩
end Malliavin
