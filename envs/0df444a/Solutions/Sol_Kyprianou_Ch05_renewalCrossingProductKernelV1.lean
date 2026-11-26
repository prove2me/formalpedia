-- Prove2me | solution 1 for Kyprianou.Ch05.renewalCrossingProductKernelV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:05:19.969252+00:00
-- url     : https://prove2.me/submissions/7ab24405-29a3-477a-a75e-f1e6ebd92e17

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

open Classical in
theorem solution
    (V F : Measure ℝ) [SFinite F]
    (x : ℝ) (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA2 : A ⊆ Ioi 0) :
    (V.prod F) {p : ℝ × ℝ | p.1 ∈ Icc 0 x ∧ p.2-(x-p.1) ∈ A ∧ x-p.1 ∈ B} =
      ∫⁻ v in Icc (0 : ℝ) x,
        (∫⁻ z in Ioi (x-v),
          (if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0) ∂F) ∂V := by
  let C : Set (ℝ × ℝ) := {p | p.1 ∈ Icc (0 : ℝ) x ∧
    p.2-(x-p.1) ∈ A ∧ x-p.1 ∈ B}
  have hC : MeasurableSet C :=
    (measurable_fst measurableSet_Icc).inter
      (((measurable_snd.sub (measurable_const.sub measurable_fst)) hA).inter
        ((measurable_const.sub measurable_fst) hB))
  change (V.prod F) C = _
  rw [Measure.prod_apply hC,← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro v
  by_cases hv : v ∈ Icc (0 : ℝ) x
  · rw [Set.indicator_of_mem hv]
    let D : Set ℝ := {z | z-(x-v) ∈ A ∧ x-v ∈ B}
    have hD : MeasurableSet D := ((measurable_id.sub measurable_const) hA).inter
      (measurable_const hB)
    have hEq : Prod.mk v ⁻¹' C = D ∩ Ioi (x-v) := by
      ext z
      simp only [C,D,mem_preimage,mem_setOf_eq,mem_inter_iff,mem_Ioi,hv,true_and]
      constructor
      · intro h
        have hp : 0 < z-(x-v) := hA2 h.1
        exact ⟨h,by linarith⟩
      · exact fun h => h.1
    rw [hEq,← Measure.restrict_apply hD,← lintegral_indicator_one hD]
    apply lintegral_congr
    intro z
    simp [D,Set.indicator_apply]
  · rw [Set.indicator_of_notMem hv]
    have hEmpty : Prod.mk v ⁻¹' C = ∅ := by
      ext z
      exact ⟨fun h => (hv h.1).elim,fun h => (notMem_empty _ h).elim⟩
    rw [hEmpty,measure_empty]
