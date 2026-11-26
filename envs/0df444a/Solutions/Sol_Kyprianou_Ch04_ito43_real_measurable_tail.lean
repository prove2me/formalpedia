-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_real_measurable_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:48:58.036996+00:00
-- url     : https://prove2.me/submissions/304d077d-cfe8-4e69-a30a-54e2fe26add3

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal Topology
set_option autoImplicit false

/-- A finite real measurable random variable admits a deterministic upper bound
outside a set of arbitrarily small probability. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (M : Ω → ℝ) (hM : Measurable M)
    (e : ℝ) (he : 0 < e) : ∃ R : ℝ, 0 < R ∧ (P {w | R < M w}).toReal < e := by
  let S : ℕ → Set Ω := fun n => {w | (n : ℝ) < M w}
  have hs (n : ℕ) : MeasurableSet (S n) :=
    measurableSet_lt measurable_const hM
  have ha : Antitone S := by
    intro i j hij w hw
    change (j : ℝ) < M w at hw
    change (i : ℝ) < M w
    exact lt_of_le_of_lt (by exact_mod_cast hij) hw
  have hI : (⋂ n, S n) = ∅ := by
    ext w
    simp only [mem_iInter,mem_empty_iff_false,iff_false]
    intro hw
    obtain ⟨n,hn⟩ := exists_nat_gt (M w)
    exact (not_lt_of_ge hn.le) (hw n)
  have h := tendsto_measure_iInter_atTop (μ := P)
    (fun n => (hs n).nullMeasurableSet) ha ⟨0,measure_ne_top _ _⟩
  rw [hI,measure_empty] at h
  have hl : Tendsto (fun n => (P (S n)).toReal) atTop (nhds 0) :=
    ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top P (S n)) |>.mpr h
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hl e he
  refine ⟨(N+1 : ℕ),by positivity,?_⟩
  have H := hN (N+1) (Nat.le_succ N)
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg ENNReal.toReal_nonneg,S] using H
