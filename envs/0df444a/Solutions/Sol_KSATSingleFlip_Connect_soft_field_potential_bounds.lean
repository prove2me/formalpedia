-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_potential_bounds
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:14:21.914779+00:00
-- url     : https://prove2.me/submissions/880473ea-4c62-411d-93bc-4aa42a5e2e18

import Theorems.Thm_KSATSingleFlip_Connect_soft_field_mass_identity
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_weight_bounds
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect

theorem solution (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable (fun z => Real.cosh z * gW (qOf z)) ν ∧
    0 ≤ hPot ν ∧ hPot ν ≤ (massM ν).toReal := by
  have hpoint (z : ℝ) : 0 ≤ Real.cosh z*gW (qOf z) ∧ Real.cosh z*gW (qOf z) ≤ 1 := by
    obtain ⟨hq,hq1,hmass⟩ := soft_field_mass_identity z
    obtain ⟨hg,hgf,_⟩ := soft_field_weight_bounds (qOf z) (le_of_lt hq) (le_of_lt hq1)
    constructor
    · positivity
    · calc
        Real.cosh z*gW (qOf z) ≤ Real.cosh z*fW (qOf z) := mul_le_mul_of_nonneg_left hgf (le_of_lt (Real.cosh_pos z))
        _ = 1 := hmass
  have hmeas : Measurable (fun z => Real.cosh z*gW (qOf z)) := by
    unfold gW qOf
    fun_prop
  have hi : Integrable (fun z => Real.cosh z*gW (qOf z)) ν := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hpoint z).1]; exact (hpoint z).2)
  refine ⟨hi, ?_, ?_⟩
  · unfold hPot pairing
    exact integral_nonneg (fun z => (hpoint z).1)
  · unfold hPot pairing massM
    have h := integral_mono hi (integrable_const (1:ℝ)) (fun z => (hpoint z).2)
    simpa [measureReal_def] using h
