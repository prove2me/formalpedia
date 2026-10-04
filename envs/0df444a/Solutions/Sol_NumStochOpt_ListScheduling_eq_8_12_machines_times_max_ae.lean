-- Prove2me | solution 1 for NumStochOpt.ListScheduling.eq_8_12_machines_times_max_ae
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:05:31.306+00:00
-- url     : https://prove2.me/submissions/92c59173-dba6-455e-b3c5-93e2b0f344cf

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_Makespan

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

namespace E0e3cac9Aux

/-- If each term eventually satisfies `b j ≤ δ √j`, so does the running maximum. -/
lemma max_bound (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (h : ∀ δ > 0, ∀ᶠ j in atTop, b j ≤ δ * Real.sqrt j) :
    ∀ δ > 0, ∀ᶠ n in atTop, NumStochOpt.ListScheduling.maxProcTime n b ≤ δ * Real.sqrt n := by
  intro δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h δ hδ)
  have hT : Tendsto (fun n : ℕ => δ * Real.sqrt n) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hδ
  filter_upwards [hT.eventually_ge_atTop (∑ j ∈ Finset.range N, b j)] with n hn
  unfold NumStochOpt.ListScheduling.maxProcTime
  apply Real.iSup_le
  · intro j
    by_cases hj : (j : ℕ) < N
    · calc b j ≤ ∑ j ∈ Finset.range N, b j :=
            Finset.single_le_sum (fun i _ => hb i) (Finset.mem_range.2 hj)
        _ ≤ δ * Real.sqrt n := hn
    · push Not at hj
      calc b j ≤ δ * Real.sqrt ((j : ℕ) : ℝ) := hN j hj
        _ ≤ δ * Real.sqrt n := by
          gcongr
          exact_mod_cast j.2.le
  · positivity

/-- From the strong law for the squares, `b j ≤ δ √j` eventually. -/
lemma term_bound (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (E : ℝ)
    (hS : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, b i ^ 2) / n) atTop (𝓝 E)) :
    ∀ δ > 0, ∀ᶠ j in atTop, b j ≤ δ * Real.sqrt j := by
  have hA : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range (n + 1), b i ^ 2) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 E) := hS.comp (tendsto_add_atTop_nat 1)
  have hB : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at h0
    refine h0.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have h1 : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range (n + 1), b i ^ 2) / n) atTop (𝓝 E) := by
    have := hA.mul hB
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have hn'' : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have h2 : Tendsto (fun n : ℕ => b n ^ 2 / n) atTop (𝓝 0) := by
    have := h1.sub hS
    rw [sub_self] at this
    refine this.congr' (Eventually.of_forall fun n => ?_)
    simp only [Finset.sum_range_succ]
    ring
  intro δ hδ
  have hev := h2.eventually (gt_mem_nhds (show (0 : ℝ) < δ ^ 2 by positivity))
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsq : b n ^ 2 ≤ δ ^ 2 * n := by
    rw [div_lt_iff₀ hnpos] at hn
    linarith
  calc b n = Real.sqrt (b n ^ 2) := (Real.sqrt_sq (hb n)).symm
    _ ≤ Real.sqrt (δ ^ 2 * n) := Real.sqrt_le_sqrt hsq
    _ = δ * Real.sqrt n := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hδ.le]

end E0e3cac9Aux

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics NumStochOpt.ListScheduling in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : ℕ → Ω → ℝ) (hmeas : ∀ j, Measurable (p j))
    (hindep : iIndepFun p P) (hident : ∀ j, IdentDistrib (p j) (p 0) P P)
    (hnonneg : ∀ j ω, 0 ≤ p j ω) (hsq : Integrable (fun ω => p 0 ω ^ 2) P)
    (μ : ℝ) (hmean : ∫ ω, p 0 ω ∂P = μ) (hμ : 0 < μ)
    (m : ℕ → ℕ) (hm : ∀ n, 1 ≤ m n)
    (hmO : (fun n : ℕ => (m n : ℝ)) =O[atTop] (fun n : ℕ => Real.sqrt n)) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (m n : ℝ) * maxProcTime n (fun j => p j ω) / (n * μ))
      atTop (𝓝 0) := by
  have hpow : Measurable (fun x : ℝ => x ^ 2) := measurable_id.pow_const 2
  have hSL := ProbabilityTheory.strong_law_ae_real (fun i ω => p i ω ^ 2) hsq
    (fun i j hij => (hindep.indepFun hij).comp hpow hpow)
    (fun i => (hident i).comp hpow)
  obtain ⟨C, hC⟩ := hmO.bound
  filter_upwards [hSL] with ω hω
  have hb : ∀ j, 0 ≤ p j ω := fun j => hnonneg j ω
  have h1 := E0e3cac9Aux.term_bound (fun j => p j ω) hb _ hω
  have h2 := E0e3cac9Aux.max_bound (fun j => p j ω) hb h1
  set C' : ℝ := max C 1 with hC'
  have hC'pos : 0 < C' := lt_of_lt_of_le one_pos (le_max_right C 1)
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · refine Eventually.of_forall fun n => lt_of_lt_of_le ha ?_
    have hp0 : 0 ≤ maxProcTime n (fun j => p j ω) := by
      unfold maxProcTime
      exact Real.iSup_nonneg fun j => hb j
    positivity
  · have hδ : 0 < a * μ / (2 * C') := by positivity
    filter_upwards [h2 _ hδ, hC, eventually_gt_atTop 0] with n hn hCn hn0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have hp0 : 0 ≤ maxProcTime n (fun j => p j ω) := by
      unfold maxProcTime
      exact Real.iSup_nonneg fun j => hb j
    have hm' : (m n : ℝ) ≤ C' * Real.sqrt n := by
      simp only [Real.norm_eq_abs, Nat.abs_cast, abs_of_nonneg (Real.sqrt_nonneg _)] at hCn
      exact le_trans hCn (mul_le_mul_of_nonneg_right (le_max_left C 1) (Real.sqrt_nonneg _))
    have hCδ : C' * (a * μ / (2 * C')) = a * μ / 2 := by
      field_simp
    rw [div_lt_iff₀ (by positivity)]
    calc (m n : ℝ) * maxProcTime n (fun j => p j ω)
        ≤ (C' * Real.sqrt n) * (a * μ / (2 * C') * Real.sqrt n) :=
          mul_le_mul hm' hn hp0 (by positivity)
      _ = C' * (a * μ / (2 * C')) * (Real.sqrt n * Real.sqrt n) := by ring
      _ = a * μ / 2 * n := by rw [hCδ, Real.mul_self_sqrt (Nat.cast_nonneg _)]
      _ < a * (n * μ) := by nlinarith [mul_pos (mul_pos ha hμ) hnpos]
