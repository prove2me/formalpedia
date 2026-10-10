-- Prove2me | solution 1 for HunterPDE.Newtonian.secondPartial_newtonianPotential_boundary_ball
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T10:13:14.159689+00:00
-- url     : https://prove2.me/submissions/c09bbdfd-3ff4-4ed1-a14f-15b98e26c5bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MeasureTheory_fderiv_convolution_right_apply_twice
import Theorems.Thm_HunterPDE_Newtonian_tendsto_cancelled_hessian_punctured_ball
import Theorems.Thm_HunterPDE_Newtonian_integrableOn_secondPartial_sub
import Theorems.Thm_HunterPDE_Newtonian_locallyIntegrable_fundamentalSolution
import Definitions.Def_HunterPDE_Newtonian_NewtonianPotential
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

open MeasureTheory HunterPDE.Newtonian Filter ContinuousLinearMap
open scoped ContDiff Topology Convolution

theorem solution (n : ℕ) (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0 < R)
    (hsupp : tsupport f ⊆ Metric.ball x R) (i j : Fin n) :
    secondPartial (newtonianPotential n f) i j x =
      (∫ y in Metric.ball x R, secondPartial (fundamentalSolution n) i j (x - y) * (f y - f x))
        - f x * (R ^ (n - 1) *
          (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
            partialDeriv (fundamentalSolution n) i (-(R • w.1)) * w.1 j ∂volume.toSphere)) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let g : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => secondPartial (fundamentalSolution n) i j (x - y) * (f y - f x)
  have hg : IntegrableOn g (Metric.ball x R) :=
    integrableOn_secondPartial_sub n hn f (contDiff_infty.mp hf 1) x R hR i j
  have hexhaust : Tendsto (fun k : ℕ =>
      ∫ y in Metric.ball x R \ Metric.closedBall x (1 / ((k : ℝ) + 1)), g y)
      atTop (𝓝 (∫ y in Metric.ball x R, g y)) := by
    have hlim : ∀ᵐ y ∂volume.restrict (Metric.ball x R),
        Tendsto (fun k : ℕ => (Metric.closedBall x (1 / ((k : ℝ) + 1)))ᶜ.indicator g y)
          atTop (𝓝 (g y)) := by
      have hne : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), y ≠ x := by
        exact volume.ae_ne x
      filter_upwards [ae_restrict_of_ae hne] with y hy
      have hdist : 0 < dist y x := dist_pos.mpr hy
      have hevent : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < dist y x :=
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
          (eventually_lt_nhds hdist)
      apply tendsto_const_nhds.congr'
      filter_upwards [hevent] with k hk
      simp only [Set.indicator_of_mem (show y ∈ (Metric.closedBall x
        (1 / ((k : ℝ) + 1)))ᶜ from by simpa using hk)]
    have hdom := tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Metric.ball x R)) (fun y => ‖g y‖)
      (fun k => hg.aestronglyMeasurable.indicator measurableSet_closedBall.compl)
      hg.norm (fun k => Filter.Eventually.of_forall fun y => norm_indicator_le_norm_self _ _) hlim
    simpa only [integral_indicator measurableSet_closedBall.compl,
      Measure.restrict_restrict measurableSet_closedBall.compl,
      Set.inter_comm, ← Set.diff_eq] using hdom
  have hparts := tendsto_cancelled_hessian_punctured_ball n hn f
    (contDiff_infty.mp hf 2) hfc x R hR hsupp i j
  have heq := tendsto_nhds_unique hexhaust hparts
  have hconv (a : EuclideanSpace ℝ (Fin n) → ℝ) :
      (fundamentalSolution n ⋆[lsmul ℝ ℝ] a) =
        (fun z => ∫ y, fundamentalSolution n (z - y) * a y) := by
    rw [← convolution_flip]
    rfl
  have hcomm := MeasureTheory.fderiv_convolution_right_apply_twice n (fundamentalSolution n) f
    (locallyIntegrable_fundamentalSolution n hn) (contDiff_infty.mp hf 2) hfc x
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  rw [hconv f, hconv] at hcomm
  change secondPartial (newtonianPotential n f) i j x =
    (∫ y, fundamentalSolution n (x - y) * secondPartial f i j y) at hcomm
  rw [hcomm]
  change (∫ y in Metric.ball x R, g y) = _ at heq
  linarith
