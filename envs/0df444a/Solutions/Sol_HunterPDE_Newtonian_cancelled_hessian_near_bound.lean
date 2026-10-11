-- Prove2me | solution 1 for HunterPDE.Newtonian.cancelled_hessian_near_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T17:09:41.889173+00:00
-- url     : https://prove2.me/submissions/f093ebd6-be85-4053-aafb-d77e3b54f424

import Theorems.Thm_MeasureTheory_singularKernel_holder_near_bound
import Theorems.Thm_HunterPDE_Newtonian_fundamentalSolution_partial
import Theorems.Thm_HunterPDE_Newtonian_norm_secondPartial_le
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory HunterPDE.Newtonian
open scoped ContDiff NNReal
set_option autoImplicit false

theorem solution (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 < α) :
    ∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Continuous f →
      ∀ H : ℝ≥0, (∀ x y, |f x - f y| ≤ (H : ℝ) * ‖x - y‖ ^ α) →
      ∀ x : EuclideanSpace ℝ (Fin n), ∀ R : ℝ, 0 < R → ∀ i j : Fin n,
        IntegrableOn (fun y => secondPartial (fundamentalSolution n) i j (x - y) *
            (f y - f x)) (Metric.ball x R) ∧
          |∫ y in Metric.ball x R, secondPartial (fundamentalSolution n) i j (x - y) *
              (f y - f x)| ≤ (A : ℝ) * (H : ℝ) * R ^ α := by
  classical
  choose C hC hbound using (fun p : Fin n × Fin n => norm_secondPartial_le n hn p.1 p.2)
  let M : ℝ := ∑ p, C p
  have hM : 0 ≤ M := Finset.sum_nonneg (fun p _ => hC p)
  let a : ℝ := (n : ℝ) * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) * M / α
  have ha : 0 ≤ a := by dsimp [a]; positivity
  refine ⟨(⟨a, ha⟩ : ℝ≥0), ?_⟩
  intro f hf H hH x R hR i j
  have hΓ := (fundamentalSolution_partial n hn).1
  have hopen : IsOpen ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := isClosed_singleton.isOpen_compl
  have hp : ContDiffOn ℝ ∞ (partialDeriv (fundamentalSolution n) j) {0}ᶜ :=
    (hΓ.fderiv_of_isOpen hopen (by simp)).clm_apply contDiffOn_const
  have hKm : AEStronglyMeasurable (secondPartial (fundamentalSolution n) i j) volume := by
    apply Measurable.aestronglyMeasurable
    apply measurable_of_continuousOn_compl_singleton 0
    exact ((hp.fderiv_of_isOpen (m := 0) hopen (by simp)).clm_apply contDiffOn_const).continuousOn
  have hCM : C (i, j) ≤ M := Finset.single_le_sum (fun p _ => hC p) (Finset.mem_univ _)
  have hb : ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 →
      ‖secondPartial (fundamentalSolution n) i j z‖ ≤ M * ‖z‖ ^ (-(n : ℝ)) := by
    intro z hz
    exact (hbound (i, j) z hz).trans
      (mul_le_mul_of_nonneg_right hCM (Real.rpow_nonneg (norm_nonneg z) _))
  have hgm : AEStronglyMeasurable (fun z => f (x - z) - f x) volume :=
    (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.sub aestronglyMeasurable_const
  have hg : ∀ z : EuclideanSpace ℝ (Fin n), |f (x - z) - f x| ≤ (H : ℝ) * ‖z‖ ^ α := by
    intro z
    simpa only [sub_sub_cancel_left, norm_neg] using hH (x - z) x
  obtain ⟨hi, he⟩ := MeasureTheory.singularKernel_holder_near_bound n (by omega) α hα
    (secondPartial (fundamentalSolution n) i j) (fun z => f (x - z) - f x)
    hKm hgm M H hM H.coe_nonneg hb hg R hR
  have hm := Measure.measurePreserving_sub_left (volume : Measure (EuclideanSpace ℝ (Fin n))) x
  have hemb := (Homeomorph.subLeft x).measurableEmbedding
  have hs : (fun y => x - y) ⁻¹' Metric.ball 0 R = Metric.ball x R := by
    ext y
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero]
    rw [norm_sub_rev]
  have hit := (hm.integrableOn_comp_preimage hemb).2 hi
  have het := hm.setIntegral_preimage_emb hemb
    (fun z => secondPartial (fundamentalSolution n) i j z * (f (x - z) - f x))
    (Metric.ball 0 R)
  simp only [hs, Function.comp_def, sub_sub_cancel] at hit het
  refine ⟨hit, ?_⟩
  rw [het]
  change _ ≤ a * (H : ℝ) * R ^ α
  convert he using 1
  dsimp [a]
  ring
