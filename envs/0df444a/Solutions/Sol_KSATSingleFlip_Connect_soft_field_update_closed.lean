-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_update_closed
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:00:28.814691+00:00
-- url     : https://prove2.me/submissions/69403fea-7dac-4bb4-bde4-8c25b4173bb9

import Theorems.Thm_KSATSingleFlip_Connect_soft_field_unfrozen_mass_recursion
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_update_symmetric
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_finite_unfrozen_mass
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_finite_intensity
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_recursion_mass
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal

theorem solution (ν : Measure ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hsym : Measure.map (fun z : ℝ => -z) ν = ν)
    (hu : (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν) ≠ ∞) :
    IsFiniteMeasure (Rbeta β ν) ∧
    Measure.map (fun z : ℝ => -z) (Rbeta β ν) = Rbeta β ν ∧
    (massM (Rbeta β ν)).toReal = β*Real.exp (hPot ν) ∧
    (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂(Rbeta β ν)) =
      ENNReal.ofReal (β*Real.exp ((∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν).toReal)) := by
  obtain ⟨hcosh,hν⟩ := soft_field_finite_unfrozen_mass ν hu
  letI : IsFiniteMeasure ν := hν
  have hint := soft_field_finite_intensity ν hu
  have hrec := soft_field_recursion_mass ν β hβ hint
  have hu' := soft_field_unfrozen_mass_recursion ν β hβ hsym hcosh
  have heq : (∫ z, Real.cosh z ∂ν) = (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν).toReal := by
    exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun z => le_of_lt (Real.cosh_pos z))) Real.continuous_cosh.aestronglyMeasurable
  have hν' : IsFiniteMeasure (Rbeta β ν) := by
    apply (soft_field_finite_unfrozen_mass (Rbeta β ν) ?_).2
    rw [hu']
    exact ENNReal.ofReal_ne_top
  refine ⟨hν', soft_field_update_symmetric ν β hint, hrec.2, ?_⟩
  rw [hu',heq]
