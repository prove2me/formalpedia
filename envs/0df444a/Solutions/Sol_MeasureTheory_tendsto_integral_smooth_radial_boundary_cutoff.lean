-- Prove2me | solution 1 for MeasureTheory.tendsto_integral_smooth_radial_boundary_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T10:25:47.254989+00:00
-- url     : https://prove2.me/submissions/6e1c61dd-3afa-4bc2-95a0-a6a3163e8d12

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory MeasureTheory.Measure Set Metric Filter Function
open scoped Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section
namespace DirectionalBallWork

theorem transition_deriv_nonneg (t : ℝ) : 0 ≤ deriv Real.smoothTransition t :=
  Real.smoothTransition.monotone.deriv_nonneg

theorem transition_deriv_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    deriv Real.smoothTransition t = 0 := by
  apply IsLocalMin.deriv_eq_zero
  exact .of_forall fun s => by
    rw [Real.smoothTransition.zero_of_nonpos ht]
    exact Real.smoothTransition.nonneg s

theorem transition_deriv_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    deriv Real.smoothTransition t = 0 := by
  apply IsLocalMax.deriv_eq_zero
  exact .of_forall fun s => by
    rw [Real.smoothTransition.one_of_one_le ht]
    exact Real.smoothTransition.le_one s

def radialCutoff (r ε t : ℝ) : ℝ :=
  Real.smoothTransition ((r ^ 2 - t ^ 2) / ε)

theorem radialCutoff_contDiff (r ε : ℝ) : ContDiff ℝ 1 (radialCutoff r ε) := by
  apply Real.smoothTransition.contDiff.comp
  exact (contDiff_const.sub (contDiff_id.pow 2)).div_const ε

theorem radialCutoff_deriv (r ε t : ℝ) :
    deriv (radialCutoff r ε) t =
      -(2 / ε) * deriv Real.smoothTransition ((r ^ 2 - t ^ 2) / ε) * t := by
  have hs : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff : ContDiff ℝ 1 _).differentiable (by norm_num)
  have hi := ((hasDerivAt_id t).pow 2).const_sub (r ^ 2)
  have hd := (hs _).hasDerivAt.comp t (hi.div_const ε)
  change deriv (Real.smoothTransition ∘ fun z => (r ^ 2 - (id ^ 2) z) / ε) t = _
  rw [hd.deriv]
  simp
  ring

theorem radialCutoff_deriv_nonpos {r ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    deriv (radialCutoff r ε) t ≤ 0 := by
  rw [radialCutoff_deriv]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_nonneg (by norm_num) hε.le)) (transition_deriv_nonneg _)) ht

theorem radialCutoff_deriv_zero_of_outer {r ε t : ℝ}
    (hr : 0 ≤ r) (hε : 0 < ε) (ht : r ≤ t) :
    deriv (radialCutoff r ε) t = 0 := by
  rw [radialCutoff_deriv, transition_deriv_zero_of_nonpos, mul_zero, zero_mul]
  apply div_nonpos_of_nonpos_of_nonneg _ hε.le
  nlinarith

theorem radialCutoff_deriv_zero_of_inner {r ε t : ℝ}
    (hε : 0 < ε) (ht : t ^ 2 ≤ r ^ 2 - ε) :
    deriv (radialCutoff r ε) t = 0 := by
  rw [radialCutoff_deriv, transition_deriv_zero_of_one_le, mul_zero, zero_mul]
  exact (le_div_iff₀ hε).2 (by linarith)

theorem radialCutoff_deriv_mass {r ε : ℝ} (_hr : 0 < r) (hε : 0 < ε)
    (hεr : ε ≤ r ^ 2) :
    (∫ t in 0..r, -deriv (radialCutoff r ε) t) = 1 := by
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_deriv_eq_sub]
  · simp only [radialCutoff, Real.smoothTransition.zero, sub_self, zero_div]
    rw [Real.smoothTransition.one_of_one_le]
    · norm_num
    · exact (le_div_iff₀ hε).2 (by simpa)
  · intro t ht
    exact (radialCutoff_contDiff r ε).differentiable (by norm_num) t
  · exact ((radialCutoff_contDiff r ε).continuous_deriv (by norm_num)).intervalIntegrable _ _

theorem tendsto_radialCutoff_boundary {r : ℝ} (hr : 0 < r)
    {H : ℝ → ℝ} (hH : ContinuousOn H (Icc 0 r))
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hεr : ∀ k, ε k ≤ r ^ 2)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => ∫ t in 0..r, -deriv (radialCutoff r (ε k)) t * H t)
      atTop (𝓝 (H r)) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  obtain ⟨δ, hδ, hδH⟩ := Metric.continuousWithinAt_iff.mp
    (hH r ⟨hr.le, le_rfl⟩) (η / 2) (half_pos hη)
  have he : ∀ᶠ k in atTop, ε k < δ * r :=
    hεlim.eventually (gt_mem_nhds (mul_pos hδ hr))
  filter_upwards [he] with k hk
  let K : ℝ → ℝ := fun t => -deriv (radialCutoff r (ε k)) t
  have hK : Continuous K := (radialCutoff_contDiff r (ε k)).continuous_deriv_one.neg
  have hKi : IntervalIntegrable K volume 0 r := hK.intervalIntegrable _ _
  have hmass : (∫ t in 0..r, K t) = 1 := radialCutoff_deriv_mass hr (hε k) (hεr k)
  have herr : ∀ t ∈ Ioc 0 r, ‖K t * (H t - H r)‖ ≤ (η / 2) * K t := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1.le
    have htr : t ≤ r := ht.2
    have hKpos : 0 ≤ K t := neg_nonneg.mpr (radialCutoff_deriv_nonpos (hε k) ht.1.le)
    by_cases hi : t ^ 2 ≤ r ^ 2 - ε k
    · simp [K, radialCutoff_deriv_zero_of_inner (hε k) hi]
    · have hdist : dist t r < δ := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2)]
        have hs : r - t ≥ 0 := sub_nonneg.mpr ht.2
        have hsq : r * (r - t) ≤ r ^ 2 - t ^ 2 := by nlinarith
        have : r * (r - t) < δ * r := lt_of_le_of_lt hsq (by linarith)
        nlinarith
      have hval := hδH ⟨ht.1.le, ht.2⟩ hdist
      rw [Real.dist_eq] at hval
      rw [norm_mul, Real.norm_of_nonneg hKpos, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right hval.le hKpos
  have hiH : IntervalIntegrable (fun t => K t * H t) volume 0 r :=
    (hK.continuousOn.mul hH).intervalIntegrable_of_Icc hr.le
  have heq : (∫ t in 0..r, K t * H t) - H r =
      ∫ t in 0..r, K t * (H t - H r) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hiH (hKi.mul_const (H r)),
      intervalIntegral.integral_mul_const, hmass, one_mul]
  rw [Real.dist_eq, ← Real.norm_eq_abs, heq]
  have hb := intervalIntegral.norm_integral_le_of_norm_le hr.le
    (Eventually.of_forall herr) (hKi.const_mul (η / 2))
  rw [intervalIntegral.integral_const_mul, hmass, mul_one] at hb
  exact hb.trans_lt (half_lt_self hη)


end DirectionalBallWork

theorem solution {r : ℝ} (hr : 0 < r) {H : ℝ → ℝ} (hH : ContinuousOn H (Icc 0 r))
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hεr : ∀ k, ε k ≤ r ^ 2)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => ∫ t in 0..r,
      -deriv (fun s : ℝ => Real.smoothTransition ((r ^ 2 - s ^ 2) / ε k)) t * H t)
      atTop (𝓝 (H r)) := by
  exact DirectionalBallWork.tendsto_radialCutoff_boundary hr hH ε hε hεr hεlim
