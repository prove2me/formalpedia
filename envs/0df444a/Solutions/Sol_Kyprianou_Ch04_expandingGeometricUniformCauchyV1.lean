-- Prove2me | solution 1 for Kyprianou.Ch04.expandingGeometricUniformCauchyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:08:57.212261+00:00
-- url     : https://prove2.me/submissions/c8965045-b0f1-4ab3-baba-d82220bee904

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology UniformConvergence
set_option autoImplicit false

/-- Eventual geometric increments on expanding horizons imply local uniform Cauchy convergence. -/
theorem solution {E : Type} [MetricSpace E] [CompleteSpace E]
    (Y : ℕ → NNReal → E)
    (h : ∀ᶠ n : ℕ in atTop, ∀ t ≤ (n : NNReal),
      dist (Y n t) (Y (n+1) t) ≤ (2⁻¹ : ℝ)^n) :
    ∀ T : NNReal, UniformCauchySeqOn Y atTop (Icc 0 T) := by
  intro T
  obtain ⟨NT,hNT⟩ := exists_nat_ge T
  obtain ⟨NA,hNA⟩ := eventually_atTop.mp h
  let B := Icc (0 : NNReal) T
  let K := max NT NA
  let G : ℕ → B →ᵤ E := fun n => UniformFun.ofFun (fun t => Y n t)
  have hC : CauchySeq (fun n => G (n+K)) := by
    apply cauchySeq_of_edist_le_geometric_two 1 ENNReal.one_ne_top
    intro n
    apply UniformFun.edist_le.mpr
    intro t
    have ht : (t : NNReal) ≤ ((n+K : ℕ) : NNReal) :=
      t.property.2.trans (hNT.trans (by exact_mod_cast (show NT ≤ n+K by dsimp [K]; omega)))
    have hb : dist (Y (n+K) t) (Y (n+K+1) t) ≤ (2⁻¹ : ℝ)^(n+K) :=
      hNA _ (by dsimp [K]; omega) t ht
    change edist (Y (n+K) t) (Y (n+1+K) t) ≤ 1 / 2^n
    rw [show n+1+K = n+K+1 by omega,edist_dist]
    calc
      _ ≤ (2⁻¹ : ENNReal)^(n+K) := by
        convert ENNReal.ofReal_le_ofReal hb using 1
        simp [ENNReal.ofReal_pow,ENNReal.inv_pow]
      _ ≤ (2⁻¹ : ENNReal)^n := by
        rw [pow_add]
        exact mul_le_of_le_one_right'
          (pow_le_one₀ (by positivity) (by norm_num))
      _ = 1 / 2^n := by simp [div_eq_mul_inv,ENNReal.inv_pow]
  obtain ⟨g,hg⟩ := cauchySeq_tendsto_of_complete hC
  have hfull : Tendsto G atTop (𝓝 g) := (tendsto_add_atTop_iff_nat K).mp hg
  have hu := UniformFun.tendsto_iff_tendstoUniformly.mp hfull
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  obtain ⟨J,hJ⟩ := Metric.uniformCauchySeqOn_iff.mp
    hu.tendstoUniformlyOn.uniformCauchySeqOn ε hε
  exact ⟨J,fun m hm n hn t ht => hJ m hm n hn ⟨t,ht⟩ (mem_univ _)⟩
