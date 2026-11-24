-- Prove2me | solution 1 for Kyprianou.Ch03.temperedStableFiniteMassV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:58:39.880333+00:00
-- url     : https://prove2.me/submissions/1f04486d-5cc5-49d3-a396-fbfcbb8be321

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (c alpha gamma : ℝ) (hc : 0 < c) (ha : alpha < 0) (hg : 0 < gamma) :
    Kyprianou.Ch03.temperedStablePositiveMeasure c alpha gamma Set.univ < ⊤ := by
  let F (x : ℝ) := c * (x ^ (-(1+alpha)) * Real.exp (-gamma*x))
  have hi : IntegrableOn F (Ioi (0 : ℝ)) volume := by
    have hh := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1:ℝ)) (s := -(1+alpha)) (b := gamma) (by linarith) (by norm_num) hg
    simpa only [IntegrableOn, F, Real.rpow_one] using hh.const_mul c
  have hnon : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp [F]
    exact mul_nonneg hc.le (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le)
  have hfin := (hasFiniteIntegral_iff_ofReal hnon).mp hi.2
  unfold Kyprianou.Ch03.temperedStablePositiveMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hf : (fun x : ℝ => ENNReal.ofReal (if 0 < x then
      c * Real.exp (-gamma*x) / x^(1+alpha) else 0)) =
      (Ioi (0 : ℝ)).indicator (fun x => ENNReal.ofReal (F x)) := by
    funext x
    by_cases hx : 0 < x
    · rw [if_pos hx, indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
      congr 1
      dsimp [F]
      rw [Real.rpow_neg hx.le]
      ring
    · rw [if_neg hx, indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx), ENNReal.ofReal_zero]
  rw [hf, lintegral_indicator measurableSet_Ioi]
  exact hfin
