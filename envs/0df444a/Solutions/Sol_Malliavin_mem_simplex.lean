-- Prove2me | solution 1 for Malliavin.mem_simplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:44:44.02891+00:00
-- url     : https://prove2.me/submissions/7aa8e7de-08a8-4b8d-bba0-2b705e2ec280

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex

set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [LinearOrder T]
namespace Malliavin
theorem _root_.solution {n : ℕ} {t : Fin n → T} : t ∈ simplex T n ↔ StrictMono t :=
  Iff.rfl
end Malliavin
