-- Prove2me | solution 1 for ManyServerQED.Scheduling.poisson_primitive_deterministic_clock_change
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T02:33:44.453561+00:00
-- url     : https://prove2.me/submissions/c30cc3e1-4a5d-4243-ac02-44b20d3a2a9b

import Definitions.Def_ManyServerQED_Scheduling_Model

open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private theorem cadlag_rescale {x : ℝ → ℝ} (h : IsCadlag x) {c : ℝ} (hc : 0 < c) :
    IsCadlag (fun t => x (c*t)) := by
  have hmap : Continuous (fun t : ℝ => c*t) := continuous_const.mul continuous_id
  constructor
  · intro t ht
    refine (h.1 (c*t) (mul_nonneg hc.le ht)).comp hmap.continuousWithinAt ?_
    intro u hu
    exact mul_le_mul_of_nonneg_left hu hc.le
  · intro t ht
    obtain ⟨l,hl⟩ := h.2 (c*t) (mul_pos hc ht)
    refine ⟨l,hl.comp ?_⟩
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact hmap.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin (s := Iio t)] with u hu
      exact mul_lt_mul_of_pos_left hu hc

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → ℝ → ℝ} {a : ℝ} (hN : IsPoissonProcess P N a) (c : ℝ) (hc : 0 < c) :
    IsPoissonProcess P (fun ω t => N ω (c*t)) (a*c) := by
  refine ⟨mul_nonneg hN.rate_nonneg hc.le, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [mul_zero] using hN.zero
  · exact fun ω t ht => hN.nat_valued ω (c*t) (mul_nonneg hc.le ht)
  · intro ω s hs t ht hst
    exact hN.mono ω (mul_nonneg hc.le hs) (mul_nonneg hc.le ht)
      (mul_le_mul_of_nonneg_left hst hc.le)
  · exact fun ω => cadlag_rescale (hN.cadlag ω) hc
  · exact fun t => hN.meas (c*t)
  · intro m s hs hmono
    exact hN.indep_incr m (fun j => c*s j) (mul_nonneg hc.le hs)
      (fun _ _ h => mul_le_mul_of_nonneg_left (hmono h) hc.le)
  · intro s t hs hst j
    have h := hN.law (c*s) (c*t) (mul_nonneg hc.le hs) (mul_le_mul_of_nonneg_left hst hc.le) j
    rwa [show a*(c*t-c*s) = a*c*(t-s) by ring] at h
