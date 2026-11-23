-- Prove2me | solution 1 for Kyprianou.Ch02.poissonMeasureIicTendstoZeroV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:11:35.188288+00:00
-- url     : https://prove2.me/submissions/42ded933-9242-4a7d-872d-a1084185d89b

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (N : ℕ) :
    Tendsto (fun r : NNReal => ProbabilityTheory.poissonMeasure r (Set.Iic N))
      atTop (𝓝 (0 : ENNReal)) := by
  classical
  have hr : Tendsto (fun r : NNReal => (r : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hsingle (k : ℕ) :
      Tendsto (fun r : NNReal => ProbabilityTheory.poissonMeasure r {k})
        atTop (𝓝 (0 : ENNReal)) := by
    have hpow : Tendsto
        (fun r : NNReal => (r : ℝ) ^ k * Real.exp (-(r : ℝ)))
          atTop (𝓝 (0 : ℝ)) :=
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp hr
    have hdiv : Tendsto
        (fun r : NNReal =>
          ((r : ℝ) ^ k * Real.exp (-(r : ℝ))) / (Nat.factorial k : ℝ))
          atTop (𝓝 (0 : ℝ)) := by
      simpa using hpow.div_const (Nat.factorial k : ℝ)
    have hf : Tendsto
        (fun r : NNReal =>
          Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (Nat.factorial k : ℝ))
          atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_comm] using hdiv
    simpa only [ProbabilityTheory.poissonMeasure_singleton,
      ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hf
  have hset : Set.Iic N = (↑(Finset.range (N + 1)) : Set ℕ) := by
    ext j
    simp only [Set.mem_Iic, Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff]
  have hsum (r : NNReal) :
      ProbabilityTheory.poissonMeasure r (Set.Iic N) =
        ∑ k ∈ Finset.range (N + 1), ProbabilityTheory.poissonMeasure r {k} := by
    rw [hset, ← MeasureTheory.sum_measure_singleton]
  have hlim := tendsto_finsetSum (Finset.range (N + 1))
    (fun i hi => hsingle i)
  simpa only [hsum, Finset.sum_const_zero] using hlim
