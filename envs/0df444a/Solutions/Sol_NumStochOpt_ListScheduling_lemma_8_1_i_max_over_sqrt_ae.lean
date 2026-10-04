-- Prove2me | solution 1 for NumStochOpt.ListScheduling.lemma_8_1_i_max_over_sqrt_ae
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T06:29:57.387008+00:00
-- url     : https://prove2.me/submissions/990b72e5-6592-41da-a172-dfd1206722e0

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_Makespan

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology

namespace E5297738Aux

open NumStochOpt.ListScheduling

/-- Deterministic part: if `a ≥ 0` and for every `k`, eventually `(k+1)^2 a_j^2 ≤ j`,
then `max_{j<n} a_j / √n → 0`. -/
theorem det (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (h : ∀ k : ℕ, ∀ᶠ j in atTop, ((k : ℝ) + 1) ^ 2 * a j ^ 2 ≤ (j : ℝ)) :
    Tendsto (fun n : ℕ => maxProcTime n a / Real.sqrt n) atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun b hb => Eventually.of_forall fun n => ?_, fun ε hε => ?_⟩
  · have : 0 ≤ maxProcTime n a := Real.iSup_nonneg fun j => ha j
    exact lt_of_lt_of_le hb (div_nonneg this (Real.sqrt_nonneg _))
  · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h k)
    set C : ℝ := ∑ j ∈ Finset.range N, a j with hC
    have hCnn : 0 ≤ C := Finset.sum_nonneg fun j _ => ha j
    have hsq : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hCt : Tendsto (fun n : ℕ => C / Real.sqrt n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsq
    have e1 := hCt.eventually (gt_mem_nhds (half_pos hε))
    filter_upwards [e1, eventually_ge_atTop 1] with n hn1 hn2
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn2)
    have hbound : maxProcTime n a ≤ C + Real.sqrt n / ((k : ℝ) + 1) := by
      apply Real.iSup_le _ (by positivity)
      intro j
      by_cases hj : (j : ℕ) < N
      · have : a j ≤ C := by
          rw [hC]
          exact Finset.single_le_sum (fun i _ => ha i) (Finset.mem_range.2 hj)
        have : 0 ≤ Real.sqrt n / ((k : ℝ) + 1) := by positivity
        linarith
      · push_neg at hj
        have h1 := hN j hj
        have h2 : a j * ((k : ℝ) + 1) ≤ Real.sqrt n := by
          rw [← Real.sqrt_sq (mul_nonneg (ha j) hk1.le)]
          apply Real.sqrt_le_sqrt
          have : ((j : ℕ) : ℝ) ≤ n := by exact_mod_cast j.2.le
          nlinarith
        have h3 : a j ≤ Real.sqrt n / ((k : ℝ) + 1) := by
          rw [le_div_iff₀ hk1]; exact h2
        linarith
    have : maxProcTime n a / Real.sqrt n ≤ C / Real.sqrt n + 1 / ((k : ℝ) + 1) := by
      rw [div_le_iff₀ hsn]
      have : (C / Real.sqrt n + 1 / ((k : ℝ) + 1)) * Real.sqrt n
          = C + Real.sqrt n / ((k : ℝ) + 1) := by
        field_simp
      rw [this]; exact hbound
    linarith

end E5297738Aux

open MeasureTheory ProbabilityTheory Filter Topology NumStochOpt.ListScheduling in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : ℕ → Ω → ℝ) (hmeas : ∀ j, Measurable (p j))
    (hindep : iIndepFun p P) (hident : ∀ j, IdentDistrib (p j) (p 0) P P)
    (hnonneg : ∀ j ω, 0 ≤ p j ω) (hsq : Integrable (fun ω => p 0 ω ^ 2) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => maxProcTime n (fun j => p j ω) / Real.sqrt n)
      atTop (𝓝 0) := by
  have H : ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᶠ j in atTop,
      ((k : ℝ) + 1) ^ 2 * p j ω ^ 2 ≤ (j : ℝ) := by
    intro k
    set c : ℝ := ((k : ℝ) + 1) ^ 2
    have hg : Measurable fun x : ℝ => c * x ^ 2 := by fun_prop
    have heq : ∀ j : ℕ, P {ω | c * p j ω ^ 2 ∈ Set.Ioi (j : ℝ)}
        = P {ω | c * p 0 ω ^ 2 ∈ Set.Ioi (j : ℝ)} := by
      intro j
      exact ((hident j).comp hg).measure_mem_eq measurableSet_Ioi
    have hsum : (∑' j : ℕ, P {ω | c * p 0 ω ^ 2 ∈ Set.Ioi (j : ℝ)}) < ⊤ := by
      letI : MeasureSpace Ω := ⟨P⟩
      haveI : IsProbabilityMeasure (volume : Measure Ω) := ‹IsProbabilityMeasure P›
      have := tsum_prob_mem_Ioi_lt_top (X := fun ω => c * p 0 ω ^ 2)
        (hsq.const_mul c) (fun ω => by positivity)
      exact this
    have hs : (∑' j : ℕ, P {ω | c * p j ω ^ 2 ∈ Set.Ioi (j : ℝ)}) ≠ ⊤ := by
      simp_rw [heq]; exact hsum.ne
    filter_upwards [ae_eventually_notMem hs] with ω hω
    filter_upwards [hω] with j hj
    simp only [Set.mem_setOf_eq, Set.mem_Ioi, not_lt] at hj
    exact hj
  filter_upwards [ae_all_iff.2 H] with ω hω
  exact E5297738Aux.det (fun j => p j ω) (fun j => hnonneg j ω) hω
