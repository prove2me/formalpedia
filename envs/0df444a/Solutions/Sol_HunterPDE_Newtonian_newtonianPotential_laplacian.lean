-- Prove2me | solution 1 for HunterPDE.Newtonian.newtonianPotential_laplacian
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T20:56:34.326223+00:00
-- url     : https://prove2.me/submissions/251e39cb-3ccb-4ade-8f9a-49c85fd77858

import Theorems.Thm_HunterPDE_Newtonian_integrable_fundamentalSolution_mul
import Theorems.Thm_HunterPDE_Newtonian_punctured_green_identity
import Theorems.Thm_HunterPDE_Newtonian_tendsto_weighted_ball_integral_zero
import Theorems.Thm_HunterPDE_Harmonic_sphereAverage_continuousOn
import Definitions.Def_HunterPDE_Newtonian_NewtonianPotential
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Tactic.FunProp

open MeasureTheory MeasureTheory.Measure Filter Set Topology
open scoped ContDiff
open Laplacian
open HunterPDE.Newtonian HunterPDE.Harmonic

set_option maxHeartbeats 1600000 in
theorem solution (n : ℕ) (hn : 2 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    (∀ x, Integrable (fun y => fundamentalSolution n (x - y) * (Δ f) y)) ∧
      ∀ x, newtonianPotential n (Δ f) x = -f x := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let v := (EuclideanSpace.basisFun (Fin n) ℝ) (⟨0, by omega⟩ : Fin n)
  have hv : ‖v‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one _
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hd : Δ f = fun y => ∑ i : Fin n, iteratedFDeriv ℝ 2 f y ![b i, b i] :=
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f b
  have hf2 : ContDiff ℝ 2 f := contDiff_infty.mp hf 2
  have hc : Continuous (Δ f) := by
    rw [hd]
    apply continuous_finsetSum
    intro i hi
    exact hf2.continuous_iteratedFDeriv'.eval continuous_const
  have hcc : HasCompactSupport (Δ f) := by
    rw [hd]
    exact (hfc.iteratedFDeriv (𝕜 := ℝ) 2).comp_left
      (g := fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin n)) ℝ =>
        ∑ i : Fin n, A ![b i, b i]) (by simp)
  have hint : ∀ x, Integrable (fun y => fundamentalSolution n (x - y) * (Δ f) y) :=
    fun x => integrable_fundamentalSolution_mul n hn (Δ f) hc hcc x
  refine ⟨hint, ?_⟩
  intro x
  obtain ⟨C, hC⟩ := hcc.exists_bound_of_continuous hc
  have hw := tendsto_weighted_ball_integral_zero n hn v hv (Δ f) C hC x
  let : NeZero (volume.toSphere : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    ⟨Measure.toSphere_ne_zero volume⟩
  have hz : sphereAverage f x 0 = f x := by simp [sphereAverage, average_const]
  have hA : Tendsto (sphereAverage f x) (𝓝[>] 0) (𝓝 (f x)) := by
    have hh := (sphereAverage_continuousOn (x := x) (r := 1) (by norm_num)
      hf.continuous.continuousOn) 0 (by simp)
    change Tendsto (sphereAverage f x) (𝓝[Icc 0 1] 0) (𝓝 (sphereAverage f x 0)) at hh
    rw [hz] at hh
    exact hh.mono_left (nhdsWithin_le_of_mem (by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with r hr hr1
      exact ⟨hr.le, hr1.le⟩))
  have hm : Tendsto (fun r : ℝ => volume (Metric.ball x r)) (𝓝[>] 0) (𝓝 0) := by
    have hp : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ n) *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) (𝓝[>] 0) (𝓝 0) := by
      have hpr : Tendsto (fun r : ℝ => r ^ n) (𝓝[>] 0) (𝓝 0) := by
        simpa [zero_pow (show n ≠ 0 by omega)] using
          (show Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) from
            tendsto_id.mono_left nhdsWithin_le_nhds).pow n
      have hh := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hpr)
        (b := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
        (Or.inr (ne_of_lt measure_ball_lt_top))
      simpa using hh
    apply hp.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa using (addHaar_ball_of_pos volume x hr).symm
  have hi := (hint x).tendsto_setIntegral_nhds_zero hm
  have ho : Tendsto (fun r : ℝ => ∫ y in (Metric.ball x r)ᶜ,
      fundamentalSolution n (x - y) * (Δ f) y) (𝓝[>] 0)
      (𝓝 (newtonianPotential n (Δ f) x)) := by
    have hh := (tendsto_const_nhds (x := newtonianPotential n (Δ f) x)).sub hi
    simp only [sub_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall fun r => by
      change (∫ y, fundamentalSolution n (x - y) * (Δ f) y) -
        (∫ y in Metric.ball x r, fundamentalSolution n (x - y) * (Δ f) y) = _
      have hs := integral_add_compl (s := Metric.ball x r) measurableSet_ball (hint x)
      linarith
  have he : Tendsto (fun r : ℝ => ∫ y in (Metric.ball x r)ᶜ,
      fundamentalSolution n (x - y) * (Δ f) y) (𝓝[>] 0) (𝓝 (-f x)) := by
    have hh := hw.neg.sub hA
    simp only [neg_zero, zero_sub] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa only [neg_mul] using
      (punctured_green_identity n hn f hf2 hfc x v hv r hr).symm
  exact tendsto_nhds_unique ho he


