-- Prove2me | solution 1 for Malliavin.sortedBy_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:42.613583+00:00
-- url     : https://prove2.me/submissions/37f7adea-4799-4b6c-baaa-afabdd6e8749

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_mem_simplex
import Theorems.Thm_Malliavin_mem_sortedBy
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [LinearOrder T]
namespace Malliavin
theorem _root_.solution (n : ℕ) : sortedBy T n 1 = simplex T n := by
  ext t
  simp only [mem_sortedBy, Equiv.Perm.coe_one, CompTriple.comp_eq, mem_simplex]
end Malliavin
