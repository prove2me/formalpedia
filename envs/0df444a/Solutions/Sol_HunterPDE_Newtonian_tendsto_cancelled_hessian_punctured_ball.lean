-- Prove2me | solution 1 for HunterPDE.Newtonian.tendsto_cancelled_hessian_punctured_ball
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T10:36:15.719535+00:00
-- url     : https://prove2.me/submissions/0517efbe-1b73-427c-b0df-91d40896a584
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HunterPDE_Newtonian_cancelled_hessian_annulus_identity
import Theorems.Thm_HunterPDE_Newtonian_cancelled_hessian_inner_error_bound
import Theorems.Thm_HunterPDE_Newtonian_integrable_fundamentalSolution_mul
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open MeasureTheory HunterPDE.Newtonian Filter
open scoped ContDiff Topology

theorem solution (n : ℕ) (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0 < R)
    (hsupp : tsupport f ⊆ Metric.ball x R) (i j : Fin n) :
    Tendsto (fun k : ℕ =>
      ∫ y in Metric.ball x R \ Metric.closedBall x (1 / ((k : ℝ) + 1)),
        secondPartial (fundamentalSolution n) i j (x - y) * (f y - f x))
      atTop (𝓝 ((∫ y, fundamentalSolution n (x - y) * secondPartial f i j y)
        + f x * (R ^ (n - 1) *
          (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
            partialDeriv (fundamentalSolution n) i (-(R • w.1)) * w.1 j ∂volume.toSphere)))) := by
  classical
  haveI : Nonempty (Fin n) := ⟨i⟩
  let r : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hr (k : ℕ) : 0 < r k := by dsimp [r]; positivity
  have hrlim : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hrwithin : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrlim, Eventually.of_forall hr⟩
  let g : EuclideanSpace ℝ (Fin n) → ℝ := secondPartial f i j
  have hdf : ContDiff ℝ 1 (partialDeriv f j) :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hgc : Continuous g :=
    (hdf.fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const
  have hgcompact : HasCompactSupport g :=
    (hfc.fderiv_apply ℝ (EuclideanSpace.single j 1)).fderiv_apply ℝ
      (EuclideanSpace.single i 1)
  have hgsupp : tsupport g ⊆ Metric.ball x R := by
    exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans
      ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j 1)).trans hsupp)
  let a : EuclideanSpace ℝ (Fin n) → ℝ := fun y => fundamentalSolution n (x - y) * g y
  have ha : Integrable a := integrable_fundamentalSolution_mul n hn g hgc hgcompact x
  have halim : Tendsto (fun k => ∫ y in Metric.ball x R \ Metric.closedBall x (r k), a y)
      atTop (𝓝 (∫ y, a y)) := by
    have heq : (∫ y in Metric.ball x R, a y) = ∫ y, a y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hgy : g y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hgsupp h))
      simp [a, hgy]
    have hp : ∀ᵐ y ∂volume.restrict (Metric.ball x R),
        Tendsto (fun k => (Metric.closedBall x (r k))ᶜ.indicator a y) atTop (𝓝 (a y)) := by
      filter_upwards [ae_restrict_of_ae (volume.ae_ne x)] with y hy
      have hd : 0 < dist y x := dist_pos.mpr hy
      have he : ∀ᶠ k in atTop, r k < dist y x :=
        hrlim.eventually (eventually_lt_nhds hd)
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with k hk
      simp only [Set.indicator_of_mem (show y ∈ (Metric.closedBall x (r k))ᶜ
        from by simpa using hk)]
    have hdom := tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Metric.ball x R)) (fun y => ‖a y‖)
      (fun k => ha.integrableOn.aestronglyMeasurable.indicator measurableSet_closedBall.compl)
      ha.integrableOn.norm
      (fun k => Eventually.of_forall fun y => norm_indicator_le_norm_self _ _) hp
    simpa only [integral_indicator measurableSet_closedBall.compl,
      Measure.restrict_restrict measurableSet_closedBall.compl, Set.inter_comm,
      ← Set.diff_eq, heq] using hdom
  let E : ℝ → ℝ := fun s => s ^ (n - 1) *
    (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
      fundamentalSolution n (-(s • w.1)) * partialDeriv f j (x + s • w.1) * w.1 i
      + partialDeriv (fundamentalSolution n) i (-(s • w.1)) *
        (f (x + s • w.1) - f x) * w.1 j ∂volume.toSphere)
  have hkernel : Tendsto (fun s : ℝ =>
      fundamentalSolution n (s • EuclideanSpace.single i 1) * s ^ (n - 1))
      (𝓝[>] 0) (𝓝 0) := by
    have hv : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
    by_cases hn2 : n = 2
    · subst n
      have hl : Tendsto (fun s : ℝ => Real.log s * s) (𝓝[>] 0) (𝓝 0) := by
        simpa using tendsto_log_mul_rpow_nhdsGT_zero (r := 1) zero_lt_one
      have hh := hl.const_mul (-(1 / (2 * Real.pi)))
      apply (show Tendsto (fun s => -(1 / (2 * Real.pi)) * (Real.log s * s))
        (𝓝[>] 0) (𝓝 0) from by simpa using hh).congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hpos : 0 < s := hs
      simp [fundamentalSolution, norm_smul, hv, Real.norm_eq_abs, abs_of_pos hpos]
      ring
    · have hh : Tendsto (fun s : ℝ =>
          (1 / ((n : ℝ) * ((n : ℝ) - 2) * unitBallVolume n)) * s)
          (𝓝[>] 0) (𝓝 0) := by
        simpa using (show Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) from
          tendsto_id.mono_left nhdsWithin_le_nhds).const_mul
          (1 / ((n : ℝ) * ((n : ℝ) - 2) * unitBallVolume n))
      apply hh.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hpos : 0 < s := hs
      simp only [fundamentalSolution, if_neg hn2, norm_smul, Real.norm_eq_abs,
        hv, mul_one, abs_of_pos hpos]
      have he : s ^ (n - 1) = s ^ (n - 2) * s := by
        rw [← pow_succ]; congr 1; omega
      rw [he]
      field_simp [ne_of_gt hpos]
  obtain ⟨C, hC, hbound⟩ := cancelled_hessian_inner_error_bound n hn f
    (hf.of_le (by norm_num)) x i j
  have hElim : Tendsto (fun k => E (r k)) atTop (𝓝 0) := by
    have hb : Tendsto (fun k => C * (r k +
        ‖fundamentalSolution n (r k • EuclideanSpace.single i 1) * r k ^ (n - 1)‖))
        atTop (𝓝 0) := by
      simpa using (hrlim.add (hkernel.comp hrwithin).norm).const_mul C
    apply squeeze_zero_norm' _ hb
    filter_upwards [hrlim.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))]
      with k hk
    exact hbound (r k) (hr k) hk.le
  have hsum := (halim.add_const (f x * (R ^ (n - 1) *
    (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
      partialDeriv (fundamentalSolution n) i (-(R • w.1)) * w.1 j ∂volume.toSphere)))).add hElim
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [hrlim.eventually (eventually_lt_nhds hR)] with k hk
  exact (cancelled_hessian_annulus_identity n hn f hf hfc x R (r k) hR
    (hr k) hk hsupp i j).symm
