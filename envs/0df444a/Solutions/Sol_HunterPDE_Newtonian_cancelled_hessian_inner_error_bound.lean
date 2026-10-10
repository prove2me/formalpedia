-- Prove2me | solution 1 for HunterPDE.Newtonian.cancelled_hessian_inner_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T10:57:20.962266+00:00
-- url     : https://prove2.me/submissions/12b2e032-8aa1-459a-b95f-caf888dc394b

import Theorems.Thm_HunterPDE_Newtonian_fundamentalSolution_partial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory HunterPDE.Newtonian Filter Set
open scoped ContDiff Topology
set_option autoImplicit false

theorem solution (n : ℕ) (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
    ‖r ^ (n - 1) *
      (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
        fundamentalSolution n (-(r • w.1)) * partialDeriv f j (x + r • w.1) * w.1 i
        + partialDeriv (fundamentalSolution n) i (-(r • w.1)) *
          (f (x + r • w.1) - f x) * w.1 j ∂volume.toSphere)‖ ≤
      C * (r + ‖fundamentalSolution n (r • EuclideanSpace.single i 1) * r ^ (n - 1)‖) := by
  let E := EuclideanSpace ℝ (Fin n)
  let S := Metric.sphere (0 : E) 1
  obtain ⟨L, hL⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn
    (hf.continuous_fderiv (by norm_num)).continuousOn
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL x (by simp))
  let a : ℝ := ‖1 / ((n : ℝ) * unitBallVolume n)‖
  let m : ℝ := (volume.toSphere : Measure S).real univ
  have ha : 0 ≤ a := norm_nonneg _
  have hm : 0 ≤ m := measureReal_nonneg
  refine ⟨L * (1 + a) * m, by positivity, ?_⟩
  intro r hr hr1
  have hp : 0 < r ^ (n - 1) := pow_pos hr _
  let G : ℝ := ‖fundamentalSolution n (r • EuclideanSpace.single i 1)‖
  have hG : 0 ≤ G := norm_nonneg _
  have hpoint : ∀ w : S,
      ‖r ^ (n - 1) *
        (fundamentalSolution n (-(r • w.1)) * partialDeriv f j (x + r • w.1) * w.1 i
        + partialDeriv (fundamentalSolution n) i (-(r • w.1)) *
          (f (x + r • w.1) - f x) * w.1 j)‖ ≤
        L * G * r ^ (n - 1) + a * L * r := by
    intro w
    have hw : ‖w.1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using w.2
    have hwi : ‖w.1 i‖ ≤ 1 := (PiLp.norm_apply_le w.1 i).trans_eq hw
    have hwj : ‖w.1 j‖ ≤ 1 := (PiLp.norm_apply_le w.1 j).trans_eq hw
    have hnr : ‖r • w.1‖ = r := by simp [norm_smul, hr.le, hw]
    have hnneg : ‖-(r • w.1)‖ = r := by rw [norm_neg, hnr]
    have hne : -(r • w.1) ≠ 0 := norm_ne_zero_iff.mp (by rw [hnneg]; exact hr.ne')
    have hy : x + r • w.1 ∈ Metric.closedBall x 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm, hnr] using hr1
    have hd : ‖partialDeriv f j (x + r • w.1)‖ ≤ L := by
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (by simpa using hL (x + r • w.1) hy)
    have hdiff : ‖f (x + r • w.1) - f x‖ ≤ L * r := by
      simpa [hnr] using (convex_closedBall x (1 : ℝ)).norm_image_sub_le_of_norm_fderiv_le
        (fun y _ => hf.differentiable (by norm_num) y) hL
        (by simp : x ∈ Metric.closedBall x 1) hy
    have hradial : fundamentalSolution n (-(r • w.1)) =
        fundamentalSolution n (r • EuclideanSpace.single i 1) := by
      simp [fundamentalSolution, hnneg, norm_smul, abs_of_pos hr]
    have hgrad : ‖partialDeriv (fundamentalSolution n) i (-(r • w.1))‖ ≤
        a / r ^ (n - 1) := by
      have hc : ‖(-(r • w.1)) i‖ ≤ r :=
        (PiLp.norm_apply_le (-(r • w.1)) i).trans_eq hnneg
      have hc' : ‖(-(r • w.1)) i / r‖ ≤ 1 := by
        rw [norm_div, Real.norm_of_nonneg hr.le]
        exact (div_le_one hr).mpr hc
      have hpow : ‖1 / r ^ (n - 1)‖ = 1 / r ^ (n - 1) :=
        Real.norm_of_nonneg (by positivity)
      rw [(fundamentalSolution_partial n hn).2 _ hne i]
      simp only [norm_mul, norm_neg, hnneg, hpow]
      calc
        _ ≤ a * (1 / r ^ (n - 1)) * 1 := by
          exact mul_le_mul_of_nonneg_left hc' (by positivity)
        _ = _ := by ring
    rw [mul_add]
    calc
      _ ≤ ‖r ^ (n - 1) *
          (fundamentalSolution n (-(r • w.1)) * partialDeriv f j (x + r • w.1) * w.1 i)‖ +
          ‖r ^ (n - 1) * (partialDeriv (fundamentalSolution n) i (-(r • w.1)) *
            (f (x + r • w.1) - f x) * w.1 j)‖ := norm_add_le _ _
      _ ≤ r ^ (n - 1) * (G * L * 1) +
          r ^ (n - 1) * ((a / r ^ (n - 1)) * (L * r) * 1) := by
        simp only [norm_mul, Real.norm_of_nonneg hp.le, hradial]
        gcongr
      _ = L * G * r ^ (n - 1) + a * L * r := by
        field_simp
  have hi := norm_integral_le_of_norm_le_const
    (μ := (volume.toSphere : Measure S)) (Eventually.of_forall hpoint)
  rw [integral_const_mul] at hi
  have hweight : ‖fundamentalSolution n (r • EuclideanSpace.single i 1) * r ^ (n - 1)‖ =
      G * r ^ (n - 1) := by rw [norm_mul, Real.norm_of_nonneg hp.le]
  rw [hweight]
  calc
    _ ≤ (L * G * r ^ (n - 1) + a * L * r) * m := hi
    _ ≤ L * (1 + a) * m * (r + G * r ^ (n - 1)) := by
      nlinarith [mul_nonneg ha hG, mul_nonneg hL0 hr.le,
        mul_nonneg (mul_nonneg (mul_nonneg hL0 ha) hG) hp.le]
