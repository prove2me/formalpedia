-- Prove2me | solution 1 for Kyprianou.Ch04.localFiniteMarkedKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:00:21.886147+00:00
-- url     : https://prove2.me/submissions/6f9eb025-6f85-4a8d-be75-3fa022806117

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (R : Omega → Measure (Real × Real))
    (hR : ∀ S : Set (Real × Real), MeasurableSet S →
      Measurable (fun w => R w S))
    (U : Set (Real × Real)) (hU : MeasurableSet U)
    (hFin : ∀ᵐ w ∂P, R w U ≠ ⊤) :
    ∃ κ : ProbabilityTheory.Kernel Omega (Real × Real),
      (∀ w, IsFiniteMeasure (κ w)) ∧
      (∀ᵐ w ∂P, κ w = (R w).restrict U) := by
  classical
  let R' : Omega → Measure (Real × Real) := fun w =>
    if R w U = ⊤ then 0 else (R w).restrict U
  have hR' : Measurable R' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    have hEq : (fun w => R' w S) =
        fun w => if R w U = ⊤ then 0 else R w (S ∩ U) := by
      funext w
      by_cases hw : R w U = ⊤ <;> simp [R', hw, Measure.restrict_apply hS]
    rw [hEq]
    exact Measurable.ite ((hR U hU) (measurableSet_singleton ⊤))
      measurable_const (hR _ (hS.inter hU))
  let κ : ProbabilityTheory.Kernel Omega (Real × Real) := ⟨R', hR'⟩
  refine ⟨κ, ?_, ?_⟩
  · intro w
    constructor
    change R' w Set.univ < ⊤
    by_cases hw : R w U = ⊤
    · simp [R', hw]
    · simpa [R', hw] using lt_top_iff_ne_top.mpr hw
  · filter_upwards [hFin] with w hw
    change R' w = _
    simp [R', hw]
