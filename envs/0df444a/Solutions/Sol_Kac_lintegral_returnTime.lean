-- Prove2me | solution 1 for Kac.lintegral_returnTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:36:11.510289+00:00
-- url     : https://prove2.me/submissions/471a29a8-df39-4aaf-946d-af77bcf94a35

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_lintegral_returnTime_eq_tsum
public import Theorems.Thm_Kac_tsum_measure_lt_returnTime

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {A : Set α}
namespace Kac
theorem _root_.solution (hf : MeasurePreserving f μ μ) (hA : MeasurableSet A) :
    ∫⁻ x in A, (returnTime f A x : ℝ≥0∞) ∂μ = μ (⋃ k : ℕ, f^[k] ⁻¹' A) := by
  rw [lintegral_returnTime_eq_tsum hf.measurable hA, tsum_measure_lt_returnTime hf hA]
end Kac
