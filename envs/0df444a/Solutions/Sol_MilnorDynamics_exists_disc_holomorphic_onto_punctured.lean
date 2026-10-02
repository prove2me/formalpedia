-- Prove2me | solution 1 for MilnorDynamics.exists_disc_holomorphic_onto_punctured
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T07:25:59.297672+00:00
-- url     : https://prove2.me/submissions/7a0e0d6d-9b9a-4081-8d6e-ebd7ef6234f9

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

set_option autoImplicit false

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

/-- Explicit witness: constant `2` on the open unit disc; outside, the radial
retraction `z ↦ (1 - 1/‖z‖) z` (onto `ℂ`), with the two punctures sent to `2`. -/
noncomputable def P92d (z : ℂ) : ℂ :=
  if ‖z‖ < 1 then 2 else
    if ((1 - 1 / ‖z‖ : ℝ) : ℂ) * z = 0 ∨ ((1 - 1 / ‖z‖ : ℝ) : ℂ) * z = 1 then 2
    else ((1 - 1 / ‖z‖ : ℝ) : ℂ) * z

lemma P92d_ne (z : ℂ) : P92d z ∈ ({0, 1}ᶜ : Set ℂ) := by
  unfold P92d
  split_ifs with h1 h2
  · simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]; norm_num
  · simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]; norm_num
  · simpa only [mem_compl_iff, mem_insert_iff, mem_singleton_iff] using h2

lemma P92d_surj (y : ℂ) (hy : y ∈ ({0, 1}ᶜ : Set ℂ)) : ∃ z, P92d z = y := by
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hy
  obtain ⟨h0, h1⟩ := hy
  have ha : 0 < ‖y‖ := norm_pos_iff.mpr h0
  set a := ‖y‖ with ha_def
  refine ⟨((1 + 1 / a : ℝ) : ℂ) * y, ?_⟩
  have hn : ‖((1 + 1 / a : ℝ) : ℂ) * y‖ = a + 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < 1 + 1 / a), ← ha_def]
    field_simp
  have hkey : ((1 - 1 / ‖((1 + 1 / a : ℝ) : ℂ) * y‖ : ℝ) : ℂ) * (((1 + 1 / a : ℝ) : ℂ) * y)
      = y := by
    rw [hn, ← mul_assoc, ← Complex.ofReal_mul]
    have : (1 - 1 / (a + 1)) * (1 + 1 / a) = (1 : ℝ) := by
      field_simp
      ring
    rw [this, Complex.ofReal_one, one_mul]
  unfold P92d
  have hnot : ¬ ‖((1 + 1 / a : ℝ) : ℂ) * y‖ < 1 := by rw [hn]; linarith
  rw [if_neg hnot, hkey, if_neg (by tauto)]

end MilnorDynamics

open scoped OnePoint in
open Filter Set MilnorDynamics in
theorem solution :
    exists p : ℂ -> ℂ, DifferentiableOn ℂ p (Metric.ball 0 1) /\
      exists hp : MapsTo p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ),
        Set.range p = {0, 1}ᶜ := by
  refine ⟨P92d, ?_, fun z _ => P92d_ne z, ?_⟩
  · refine (differentiableOn_const (2 : ℂ)).congr ?_
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    simp only [P92d, if_pos hz]
  · ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact P92d_ne z
    · intro hy
      exact P92d_surj y hy
