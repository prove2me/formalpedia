-- Prove2me | solution 1 for Kyprianou.Ch05.finiteMeasureCellIntegralError
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:50:47.147459+00:00
-- url     : https://prove2.me/submissions/270ab1df-818c-4120-a529-bd3a6d449272

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure

open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Cell integral error controlled by pointwise error and cell mass. -/
theorem solution
    (V : Measure Real) (S : Set Real) (hM : MeasurableSet S)
    (hF : V S ≠ ⊤) (f : Real → Real) (hf : IntegrableOn f S V)
    (c e : Real) (ha : ∀ z, z ∈ S → |f z-c| ≤ e) :
    |(∫ z in S, f z ∂V) - c*(V S).toReal| ≤ e*(V S).toReal := by
  haveI : IsFiniteMeasure (V.restrict S) := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact lt_top_iff_ne_top.mpr hF⟩
  have hc : IntegrableOn (fun _ : Real => c) S V := integrableOn_const hF
  have he : ∀ᵐ z ∂V.restrict S, ‖f z-c‖ ≤ e := by
    filter_upwards [ae_restrict_mem hM] with z hz
    simpa only [Real.norm_eq_abs] using ha z hz
  have h := norm_integral_le_of_norm_le_const he
  rw [integral_sub hf hc, integral_const, Measure.real,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul,
    Real.norm_eq_abs, mul_comm (V S).toReal c] at h
  simpa only [mul_comm e] using h
