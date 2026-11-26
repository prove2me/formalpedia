-- Prove2me | solution 1 for Kyprianou.Ch04.pointwiseFiniteKernelJointRealIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:21:32.981799+00:00
-- url     : https://prove2.me/submissions/e226db34-e737-41e9-8dba-a4a9fba6ea94

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_pointwiseFiniteKernelJointLIntegral
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false

/-- A bounded jointly measurable real integrand has measurable integrals against pointwise finite random measures. -/
theorem solution {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (R : Ω → Measure E) (hR : ∀ S : Set E, MeasurableSet S → Measurable (fun w => R w S))
    (hFin : ∀ w, IsFiniteMeasure (R w))
    (g : Ω × E → ℝ) (hg : Measurable g)
    (C : ℝ) (hC : ∀ p, ‖g p‖ ≤ C) :
    Measurable (fun w => ∫ z, g (w,z) ∂(R w)) := by
  have hp := Kyprianou.Ch04.pointwiseFiniteKernelJointLIntegral R hR hFin
    (fun p => ENNReal.ofReal (g p)) (ENNReal.measurable_ofReal.comp hg)
  have hn := Kyprianou.Ch04.pointwiseFiniteKernelJointLIntegral R hR hFin
    (fun p => ENNReal.ofReal (-g p)) (ENNReal.measurable_ofReal.comp hg.neg)
  have he (w : Ω) : (∫ z, g (w,z) ∂(R w)) =
      (∫⁻ z, ENNReal.ofReal (g (w,z)) ∂(R w)).toReal -
        (∫⁻ z, ENNReal.ofReal (-g (w,z)) ∂(R w)).toReal := by
    letI : IsFiniteMeasure (R w) := hFin w
    have hi : Integrable (fun z => g (w,z)) (R w) :=
      (MemLp.of_bound (hg.comp measurable_prodMk_left).aestronglyMeasurable C
        (Eventually.of_forall fun z => hC (w,z)) : MemLp (fun z => g (w,z)) 1 (R w)).integrable le_rfl
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi
  simp_rw [he]
  exact hp.ennreal_toReal.sub hn.ennreal_toReal
