-- Prove2me | solution 1 for Kac.lintegral_returnTime_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:53:24.569992+00:00
-- url     : https://prove2.me/submissions/008375a3-e3fa-4224-a365-6068df5a0bb0

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_iInter_notYet
public import Theorems.Thm_Kac_measurableSet_iUnion_preimage_iterate
public import Theorems.Thm_Kac_lintegral_returnTime
public import Theorems.Thm_Kac_measure_iInter_notYet_eq_zero

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
    ∫⁻ x in A, (returnTime f A x : ℝ≥0∞) ∂μ = 1 := by
  rw [lintegral_returnTime hf.toMeasurePreserving hA]
  have hU := measurableSet_iUnion_preimage_iterate hf.toMeasurePreserving.measurable hA
  have h0 : μ (⋃ k : ℕ, f^[k] ⁻¹' A)ᶜ = 0 := by
    rw [← iInter_notYet]
    exact measure_iInter_notYet_eq_zero hf hA hA0
  rw [prob_compl_eq_one_sub hU, tsub_eq_zero_iff_le] at h0
  exact le_antisymm prob_le_one h0
end Kac
