-- Prove2me | solution 1 for Malliavin.ae_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:03.708686+00:00
-- url     : https://prove2.me/submissions/8cd01f8e-7fbb-4d2c-b452-42a73f6060bf

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_measure_diagonal_eq_zero

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
    ∀ᵐ t ∂(Measure.pi fun _ : Fin n => μ), Function.Injective t :=
  ae_iff.2 (measure_diagonal_eq_zero n)
end Malliavin
