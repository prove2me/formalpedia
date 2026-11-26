-- Prove2me | solution 1 for Malliavin.measurableSet_sortedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:57.191864+00:00
-- url     : https://prove2.me/submissions/35f2af20-df6e-4eaf-9933-24a0dc9a54fe

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_measurable_comp_perm
import Theorems.Thm_Malliavin_measurableSet_simplex

set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] [TopologicalSpace T] [LinearOrder T] [OrderClosedTopology T]
  [SecondCountableTopology T] [OpensMeasurableSpace T]
namespace Malliavin
theorem _root_.solution (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MeasurableSet (sortedBy T n σ) :=
  (measurableSet_simplex n).preimage (measurable_comp_perm n σ)
end Malliavin
