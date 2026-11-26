-- Prove2me | solution 1 for Malliavin.measurableSet_simplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:45:30.371676+00:00
-- url     : https://prove2.me/submissions/317d94b8-a1ca-4ba2-a443-8435310cb50a

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_mem_simplex
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] [TopologicalSpace T] [LinearOrder T] [OrderClosedTopology T]
  [SecondCountableTopology T] [OpensMeasurableSpace T]
namespace Malliavin
theorem _root_.solution (n : ℕ) : MeasurableSet (simplex T n) := by
  have : simplex T n =
      ⋂ (i : Fin n) (j : Fin n) (_ : i < j), {t : Fin n → T | t i < t j} := by
    ext t
    simp only [mem_simplex, Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
end Malliavin
