-- Prove2me | solution 1 for Malliavin.measure_diagonal_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:27.227433+00:00
-- url     : https://prove2.me/submissions/be90ec3e-6276-4ae3-8ff0-fd4170c419fa

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_diagonal_eq_iUnion
import Theorems.Thm_Malliavin_measure_coord_eq_zero

set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] [TopologicalSpace T] [LinearOrder T] [OrderClosedTopology T]
  [SecondCountableTopology T] [OpensMeasurableSpace T]
variable {μ : Measure T} [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Malliavin
theorem _root_.solution [NullSingletonClass μ] (n : ℕ) :
    Measure.pi (fun _ : Fin n => μ) (diagonal T n) = 0 := by
  rw [diagonal_eq_iUnion]
  exact measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij =>
    measure_coord_eq_zero hij
end Malliavin
