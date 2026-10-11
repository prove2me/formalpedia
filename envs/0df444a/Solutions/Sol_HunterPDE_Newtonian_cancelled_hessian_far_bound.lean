-- Prove2me | solution 1 for HunterPDE.Newtonian.cancelled_hessian_far_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T18:05:16.539991+00:00
-- url     : https://prove2.me/submissions/6e62f747-7f4c-48bf-9e1f-621ad831c2d2

import Theorems.Thm_HunterPDE_Newtonian_secondPartial_difference_le
import Theorems.Thm_HunterPDE_Newtonian_norm_fderiv_secondPartial_le
import Theorems.Thm_MeasureTheory_radial_majorant_exterior_bound
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open MeasureTheory HunterPDE.Newtonian
open scoped NNReal

theorem solution (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Continuous f →
      ∀ H : ℝ≥0, (∀ x y, |f x - f y| ≤ (H : ℝ) * ‖x - y‖ ^ α) →
      ∀ m h : EuclideanSpace ℝ (Fin n), h ≠ 0 → ∀ i j : Fin n,
        IntegrableOn (fun z =>
          (secondPartial (fundamentalSolution n) i j (z + h) -
            secondPartial (fundamentalSolution n) i j (z - h)) *
          (f (m - z) - f (m + h))) (Metric.closedBall 0 (2 * ‖h‖))ᶜ ∧
        |∫ z in (Metric.closedBall 0 (2 * ‖h‖))ᶜ,
          (secondPartial (fundamentalSolution n) i j (z + h) -
            secondPartial (fundamentalSolution n) i j (z - h)) *
          (f (m - z) - f (m + h))| ≤ A * (H : ℝ) * (2 * ‖h‖) ^ α := by
  obtain ⟨C, hC, hdiff⟩ := secondPartial_difference_le n hn
  let D := C * (2 : ℝ) ^ α
  let A := (n : ℝ) * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) * D / (1 - α)
  have hden : 0 < 1 - α := sub_pos.mpr hα₁
  refine ⟨A, by dsimp [A, D]; positivity, ?_⟩
  intro f hf H hH m h hh i j
  let K := secondPartial (fundamentalSolution n) i j
  have hKm : Measurable K := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz
    exact ((norm_fderiv_secondPartial_le n hn).choose_spec.2 i j z hz0).1.continuousAt.continuousWithinAt
  let F := fun z => (K (z + h) - K (z - h)) * (f (m - z) - f (m + h))
  have hFm : AEStronglyMeasurable F volume := by
    exact ((hKm.comp (continuous_id.add continuous_const).measurable).sub
      (hKm.comp (continuous_id.sub continuous_const).measurable)).aestronglyMeasurable.mul
      ((hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.sub aestronglyMeasurable_const)
  have hδ : 0 < 2 * ‖h‖ := mul_pos (by norm_num) (norm_pos_iff.mpr hh)
  have hb (z : EuclideanSpace ℝ (Fin n)) (hz : 2 * ‖h‖ < ‖z‖) :
      ‖F z‖ ≤ D * (H : ℝ) * (2 * ‖h‖) * ‖z‖ ^ (α - n - 1) := by
    have hzr : 0 < ‖z‖ := hδ.trans hz
    have hzh : ‖h‖ ≤ ‖z‖ / 2 := by linarith
    have hd := hdiff i j z h (norm_pos_iff.mp hzr) hzh
    have hg : |f (m - z) - f (m + h)| ≤ (H : ℝ) * ‖z + h‖ ^ α := by
      have he : (m - z) - (m + h) = -(z + h) := by module
      simpa only [he, norm_neg] using hH (m - z) (m + h)
    have hnz : ‖z + h‖ ≤ 2 * ‖z‖ := (norm_add_le z h).trans (by linarith)
    have hp := Real.rpow_le_rpow (norm_nonneg (z + h)) hnz hα₀.le
    have he : ‖z‖ ^ (-(n : ℝ) - 1) * ‖z‖ ^ α = ‖z‖ ^ (α - n - 1) := by
      rw [← Real.rpow_add hzr]
      congr 1
      ring
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      _ ≤ (C * ‖h‖ * ‖z‖ ^ (-(n : ℝ) - 1)) * ((H : ℝ) * ‖z + h‖ ^ α) :=
        mul_le_mul hd hg (abs_nonneg _) (by positivity)
      _ ≤ (C * (2 * ‖h‖) * ‖z‖ ^ (-(n : ℝ) - 1)) * ((H : ℝ) * (2 * ‖z‖) ^ α) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg h]) hC) (by positivity)
        · exact mul_le_mul_of_nonneg_left hp H.coe_nonneg
        · positivity
        · positivity
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg z)]
        calc
          _ = (C * (2 : ℝ) ^ α) * (H : ℝ) * (2 * ‖h‖) *
            (‖z‖ ^ (-(n : ℝ) - 1) * ‖z‖ ^ α) := by ring
          _ = _ := by rw [he]
  obtain ⟨hi, he⟩ := MeasureTheory.radial_majorant_exterior_bound n (by omega) α hα₁ F hFm D H (2 * ‖h‖) hδ hb
  refine ⟨hi, ?_⟩
  change _ ≤ A * (H : ℝ) * (2 * ‖h‖) ^ α
  convert he using 1
  dsimp [A]
  ring
