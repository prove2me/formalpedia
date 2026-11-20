-- Prove2me | solution 1 for LevyStochCalc.Brownian.Martingale.brownianMotion_integrable
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T13:44:54.163312+00:00
-- url     : https://prove2.me/submissions/b40b2f39-f540-480b-903a-475e6ce209fd

import Definitions.Def_LevyStochCalc_Brownian_Martingale_F000
import Mathlib.Probability.Distributions.Gaussian.Real
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem bm_memLp2 {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (s : ℝ) :
    MeasureTheory.MemLp (W.W s) 2 P := by
  rcases lt_or_ge 0 s with hs | hs
  · -- W_s = W_s - W_0 a.e., and the increment is N(0, s)
    have hae : (fun ω => W.W s ω - W.W 0 ω) =ᵐ[P] W.W s := by
      filter_upwards [W.initial_zero] with ω h; simp [h]
    refine MemLp.ae_eq hae ?_
    have hm : Measurable (fun ω => W.W s ω - W.W 0 ω) :=
      (W.measurable_eval s).sub (W.measurable_eval 0)
    have hlaw := W.increment_gaussian (le_refl 0) hs
    have h2 : MemLp id 2 (P.map (fun ω => W.W s ω - W.W 0 ω)) := by
      rw [hlaw]; exact memLp_id_gaussianReal' 2 (by norm_num)
    exact (memLp_map_measure_iff aestronglyMeasurable_id hm.aemeasurable).mp h2
  · have hz : W.W s =ᵐ[P] 0 := by
      rcases hs.lt_or_eq with h | h
      · filter_upwards [W.negative_zero s h] with ω hω; simp [hω]
      · subst h; filter_upwards [W.initial_zero] with ω hω; simp [hω]
    exact (MemLp.zero).ae_eq hz.symm

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (s : ℝ) :
    MeasureTheory.Integrable (W.W s) P :=
  (bm_memLp2 W s).integrable (by norm_num)
