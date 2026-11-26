-- Prove2me | solution 1 for Malliavin.measurableSet_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:50.631343+00:00
-- url     : https://prove2.me/submissions/78e5eb51-7a87-4de7-b342-a6fdd4f087af

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_diagonal_eq_iUnion
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
theorem _root_.solution (n : ℕ) : MeasurableSet (diagonal T n) := by
  rw [diagonal_eq_iUnion]
  refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun _ => ?_
  have : {t : Fin n → T | t i = t j} = {t | t i ≤ t j} ∩ {t | t j ≤ t i} := by
    ext t
    simp only [le_antisymm_iff, mem_ofPred_eq, mem_inter_iff]
  rw [this]
  exact (measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)).inter
    (measurableSet_le (measurable_pi_apply j) (measurable_pi_apply i))
end Malliavin
