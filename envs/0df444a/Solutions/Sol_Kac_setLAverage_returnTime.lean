-- Prove2me | solution 1 for Kac.setLAverage_returnTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:58:08.79191+00:00
-- url     : https://prove2.me/submissions/a07c526a-9fa2-4039-8409-37481fa80319

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_lintegral_returnTime_eq_one

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {A : Set α}
variable [IsProbabilityMeasure μ]
namespace Kac
theorem _root_.solution (hf : Ergodic f μ) (hA : MeasurableSet A) (hA0 : μ A ≠ 0) :
    ⨍⁻ x in A, (returnTime f A x : ℝ≥0∞) ∂μ = (μ A)⁻¹ := by
  rw [setLAverage_eq, lintegral_returnTime_eq_one hf hA hA0, one_div]
end Kac
