-- Prove2me | solution 1 for Kac.lintegral_returnTime_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:24:34.256883+00:00
-- url     : https://prove2.me/submissions/c6ce57bb-63c1-4e25-8311-d60fcc29069b

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_notYet_zero
public import Theorems.Thm_Kac_notYet_succ
public import Theorems.Thm_Kac_setOf_lt_returnTime
public import Theorems.Thm_Kac_toENNReal_eq_tsum
public import Theorems.Thm_Kac_measurableSet_notYet
attribute [local simp] Kac.notYet_zero
attribute [local simp] Kac.notYet_succ

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {A : Set α}
namespace Kac
theorem _root_.solution (hf : Measurable f) (hA : MeasurableSet A) :
    ∫⁻ x in A, (returnTime f A x : ℝ≥0∞) ∂μ
      = ∑' n : ℕ, μ (A ∩ {x | (n : ℕ∞) < returnTime f A x}) := by
  have hmeas : ∀ n : ℕ, MeasurableSet {x | (n : ℕ∞) < returnTime f A x} := fun n => by
    rw [setOf_lt_returnTime]
    exact hf (measurableSet_notYet hf hA n)
  calc ∫⁻ x in A, (returnTime f A x : ℝ≥0∞) ∂μ
      = ∫⁻ x in A, ∑' n : ℕ, {x | (n : ℕ∞) < returnTime f A x}.indicator 1 x ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [toENNReal_eq_tsum]
        congr 1
        funext n
        simp [Set.indicator_apply]
    _ = ∑' n : ℕ, ∫⁻ x in A, {x | (n : ℕ∞) < returnTime f A x}.indicator 1 x ∂μ :=
        lintegral_tsum fun n => (measurable_one.indicator (hmeas n)).aemeasurable
    _ = ∑' n : ℕ, μ (A ∩ {x | (n : ℕ∞) < returnTime f A x}) := by
        congr 1
        funext n
        rw [lintegral_indicator_one (hmeas n), Measure.restrict_apply (hmeas n), inter_comm]
end Kac
