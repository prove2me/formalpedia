-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_finite_unfrozen_mass
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:00:26.449303+00:00
-- url     : https://prove2.me/submissions/fe05b525-1d2b-4997-8019-295c10db0574

import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

theorem solution (ν : Measure ℝ)
    (hu : (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν) ≠ ∞) :
    Integrable Real.cosh ν ∧ IsFiniteMeasure ν := by
  have hcosh0 : 0 ≤ᵐ[ν] Real.cosh := Filter.Eventually.of_forall (fun z => le_of_lt (Real.cosh_pos z))
  have hcoshfin : HasFiniteIntegral Real.cosh ν := (hasFiniteIntegral_iff_ofReal hcosh0).2 (lt_top_iff_ne_top.mpr hu)
  have hcoshi : Integrable Real.cosh ν := ⟨Real.continuous_cosh.aestronglyMeasurable, hcoshfin⟩
  have hν : ν Set.univ < ∞ := by
    calc
      ν Set.univ = ∫⁻ _z : ℝ, (1:ℝ≥0∞) ∂ν := (lintegral_one).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν := by
        apply lintegral_mono
        intro z
        have hh := ENNReal.ofReal_le_ofReal (Real.one_le_cosh z)
        simpa using hh
      _ < ∞ := lt_top_iff_ne_top.mpr hu
  exact ⟨hcoshi, ⟨hν⟩⟩
