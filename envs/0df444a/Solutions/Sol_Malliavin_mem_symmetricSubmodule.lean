-- Prove2me | solution 1 for Malliavin.mem_symmetricSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:42:33.952068+00:00
-- url     : https://prove2.me/submissions/b466c235-53a9-4298-a981-62c2b3c5244e

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
theorem _root_.solution {n : ℕ} {f : (Fin n → T) → E} :
    f ∈ symmetricSubmodule T E n ↔ IsSymmetric n f :=
  Iff.rfl
end Malliavin
