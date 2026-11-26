-- Prove2me | solution 1 for Malliavin.IsSymmetric.comp_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:35.639242+00:00
-- url     : https://prove2.me/submissions/ce7f78bd-0bf0-48a1-9146-b69fb5be61f2

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
namespace Malliavin
namespace IsSymmetric
theorem _root_.solution {n : ℕ} {g : (Fin n → T) → E} (hg : IsSymmetric n g)
    {F : Type*} (φ : E → F) : IsSymmetric n (φ ∘ g) :=
  fun σ t => by simp only [Function.comp_apply, hg σ t]
end IsSymmetric
end Malliavin
