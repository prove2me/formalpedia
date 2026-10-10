-- Prove2me | solution 1 for MeasureTheory.integrableOn_singularKernel_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T10:12:30.419517+00:00
-- url     : https://prove2.me/submissions/b499a2d7-a7a6-4893-a87a-e846d040f617

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped ContDiff
set_option autoImplicit false

theorem solution (n : ℕ) (hn : 1 ≤ n)
    (K f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hK : AEStronglyMeasurable K volume) (hf : ContDiff ℝ 1 f)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z, z ≠ 0 → ‖K z‖ ≤ C * ‖z‖ ^ (-(n : ℝ)))
    (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun z => K z * (f z - f 0)) (Metric.ball 0 R) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).exists_bound_of_continuousOn
    (hf.continuous_fderiv (by norm_num)).continuousOn
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0 (by simp [hR.le]))
  have hdiff : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
      ‖f z - f 0‖ ≤ L * ‖z‖ := by
    intro z hz
    simpa using (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).norm_image_sub_le_of_norm_fderiv_le
        (x := 0) (y := z)
        (fun y _ => hf.differentiable (by norm_num) y) hL
        (by simp [hR.le]) (Metric.ball_subset_closedBall hz)
  refine integrableOn_ball_of_norm_le_rpow (C := C * L) (α := (n : ℝ) - 1)
    (by simpa using hn) ?_ ?_ ?_
  · simp only [finrank_euclideanSpace, Fintype.card_fin]
    linarith
  · have hne : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), z ≠ 0 :=
      by simp [ae_iff]
    filter_upwards [ae_restrict_of_ae hne, self_mem_ae_restrict measurableSet_ball] with z hz hzR
    have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
    calc
      ‖K z * (f z - f 0)‖ = ‖K z‖ * ‖f z - f 0‖ := norm_mul _ _
      _ ≤ (C * ‖z‖ ^ (-(n : ℝ))) * (L * ‖z‖) :=
        mul_le_mul (hbound z hz) (hdiff z hzR) (norm_nonneg _) (by positivity)
      _ = C * L * ‖z‖ ^ (-((n : ℝ) - 1)) := by
        rw [show -((n : ℝ) - 1) = -(n : ℝ) + 1 by ring, Real.rpow_add hp, Real.rpow_one]
        ring
  · exact hK.mul (hf.continuous.aestronglyMeasurable.sub aestronglyMeasurable_const)
