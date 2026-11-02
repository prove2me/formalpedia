-- Prove2me | solution 1 for NaiveLearn.OverMatch.weighted_lln
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T12:45:19.559474+00:00
-- url     : https://prove2.me/submissions/77fde7d5-a2ab-4751-bf82-2836063f321d

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model
import Theorems.Thm_NaiveLearn_OverMatch_posterior_mean_gt_lt

open MeasureTheory ProbabilityTheory Filter Topology
open NaiveLearn.OverMatch

/-- The posterior is measurable and bounded by `1` almost surely in both states. -/
lemma NL_post_bound (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {S : Type*} [MeasurableSpace S] (F0 F1 : Measure S)
    [IsProbabilityMeasure F0] [IsProbabilityMeasure F1] :
    Measurable (posterior p F0 F1) ∧ (∀ᵐ s ∂F1, ‖posterior p F0 F1 s‖ ≤ 1) ∧
      (∀ᵐ s ∂F0, ‖posterior p F0 F1 s‖ ≤ 1) := by
  set a : ENNReal := ENNReal.ofReal p with ha
  set b : ENNReal := ENNReal.ofReal (1 - p) with hb
  set ν : Measure S := a • F1 + b • F0 with hν
  have hxdef : ∀ s, posterior p F0 F1 s = ((a • F1).rnDeriv ν s).toReal := fun s => rfl
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have ha0 : a ≠ 0 := by simp [ha, hp0]
  have hb0 : b ≠ 0 := by simp [hb, hp1]
  have : IsFiniteMeasure (a • F1) := by
    constructor; rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]; exact hat.lt_top
  have : IsFiniteMeasure (b • F0) := by
    constructor; rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact ENNReal.ofReal_lt_top
  have : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have hle : a • F1 ≤ ν := Measure.le_add_right le_rfl
  have hle1 : ∀ᵐ s ∂ν, (a • F1).rnDeriv ν s ≤ 1 := Measure.rnDeriv_le_one_of_le hle
  have hxb : ∀ᵐ s ∂ν, ‖posterior p F0 F1 s‖ ≤ 1 := by
    filter_upwards [hle1] with s hs
    rw [hxdef, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hs
  have hF1 : F1 ≪ ν := (Measure.absolutelyContinuous_smul ha0).trans
    (Measure.AbsolutelyContinuous.add_right Measure.AbsolutelyContinuous.rfl _)
  have hF0 : F0 ≪ ν := (Measure.absolutelyContinuous_smul hb0).trans
    (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl))
  exact ⟨(Measure.measurable_rnDeriv _ _).ennreal_toReal, hF1.ae_le hxb, hF0.ae_le hxb⟩

/-- Chebyshev bound for a weighted sum of i.i.d. bounded variables. -/
lemma NL_cheb {S : Type*} [MeasurableSpace S] (F : Measure S) [IsProbabilityMeasure F]
    (x : S → ℝ) (hxm : Measurable x) (hxb : ∀ᵐ s ∂F, ‖x s‖ ≤ 1)
    {N : ℕ} (μ : Fin N → ℝ) (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : ∑ i, μ i = 1) {c : ℝ} (hc : 0 < c) :
    (Measure.pi fun _ : Fin N => F) {s | c ≤ |∑ i, μ i * x (s i) - ∫ y, x y ∂F|} ≤
      ENNReal.ofReal ((⨆ i, μ i) / c ^ 2) := by
  set P : Measure (Fin N → S) := Measure.pi fun _ : Fin N => F
  have hxL : MemLp x 2 F := MemLp.of_bound hxm.aestronglyMeasurable 1 hxb
  have hXL : ∀ i, MemLp (fun y => μ i * x y) 2 F := fun i => hxL.const_mul (μ i)
  have hYfun : (fun s : Fin N → S => ∑ i, μ i * x (s i)) =
      ∑ i, fun s : Fin N → S => (fun y => μ i * x y) (s i) := by
    funext s; simp [Finset.sum_apply]
  have hYL : MemLp (fun s : Fin N → S => ∑ i, μ i * x (s i)) 2 P := by
    rw [hYfun]
    exact memLp_finsetSum' _ fun i _ =>
      (hXL i).comp_measurePreserving (measurePreserving_eval _ i)
  have hmean : ∫ s, ∑ i, μ i * x (s i) ∂P = ∫ y, x y ∂F := by
    rw [integral_finset_sum]
    · simp_rw [integral_const_mul]
      have : ∀ i : Fin N, ∫ s, x (s i) ∂P = ∫ y, x y ∂F := fun i =>
        integral_comp_eval (μ := fun _ : Fin N => F) hxm.aestronglyMeasurable
      simp_rw [this, ← Finset.sum_mul, hμ1, one_mul]
    · intro i _
      exact ((hXL i).comp_measurePreserving (measurePreserving_eval _ i)).integrable
        one_le_two
  have hvar : variance (fun s : Fin N → S => ∑ i, μ i * x (s i)) P ≤ ⨆ i, μ i := by
    rw [hYfun, variance_sum_pi hXL]
    simp_rw [variance_const_mul]
    have hvx : variance x F ≤ 1 := by
      refine (variance_le_expectation_sq hxm.aestronglyMeasurable).trans ?_
      have : ∫ y, (x ^ 2) y ∂F ≤ ∫ _y, (1 : ℝ) ∂F := by
        apply integral_mono_ae
        · exact hxL.integrable_sq
        · exact integrable_const _
        · filter_upwards [hxb] with y hy
          simp only [Pi.pow_apply]
          rw [Real.norm_eq_abs] at hy
          nlinarith [abs_nonneg (x y), sq_abs (x y)]
      simpa using this
    have hvx0 : 0 ≤ variance x F := variance_nonneg _ _
    have hbdd : BddAbove (Set.range μ) := Set.finite_range μ |>.bddAbove
    calc ∑ i, μ i ^ 2 * variance x F ≤ ∑ i, μ i * (⨆ j, μ j) := by
          apply Finset.sum_le_sum
          intro i _
          have h1 : μ i ≤ ⨆ j, μ j := le_ciSup hbdd i
          have h2 : μ i ^ 2 * variance x F ≤ μ i ^ 2 := by
            nlinarith [sq_nonneg (μ i)]
          nlinarith [hμ0 i]
      _ = ⨆ j, μ j := by rw [← Finset.sum_mul, hμ1, one_mul]
  have hch := meas_ge_le_variance_div_sq hYL hc
  rw [hmean] at hch
  refine hch.trans (ENNReal.ofReal_le_ofReal ?_)
  exact div_le_div_of_nonneg_right hvar (sq_nonneg c)

theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {S : Type*} [MeasurableSpace S] (F0 F1 : Measure S)
    [IsProbabilityMeasure F0] [IsProbabilityMeasure F1] (hF : F0 ≠ F1)
    (n : ℕ → ℕ) (μ : ∀ k, Fin (n k) → ℝ) (hμ0 : ∀ k i, 0 ≤ μ k i) (hμ1 : ∀ k, ∑ i, μ k i = 1)
    (hvan : Tendsto (fun k => ⨆ i, μ k i) atTop (𝓝 0)) :
    Tendsto (fun k => (Measure.pi fun _ : Fin (n k) => F1)
        {s | p < ∑ i, μ k i * posterior p F0 F1 (s i)}) atTop (𝓝 1) ∧
    Tendsto (fun k => (Measure.pi fun _ : Fin (n k) => F0)
        {s | ∑ i, μ k i * posterior p F0 F1 (s i) < p}) atTop (𝓝 1) := by
  obtain ⟨hm1, hm0⟩ := posterior_mean_gt_lt p hp0 hp1 F0 F1 hF
  obtain ⟨hxm, hb1, hb0⟩ := NL_post_bound p hp0 hp1 F0 F1
  set x := posterior p F0 F1
  -- generic squeeze
  have squeeze : ∀ (g : ℝ), 0 < g → ∀ (u : ℕ → ENNReal),
      (∀ k, 1 - ENNReal.ofReal ((⨆ i, μ k i) / g ^ 2) ≤ u k) → (∀ k, u k ≤ 1) →
      Tendsto u atTop (𝓝 1) := by
    intro g hg u hlow hup
    have h1 : Tendsto (fun k => ENNReal.ofReal ((⨆ i, μ k i) / g ^ 2)) atTop (𝓝 0) := by
      have := (hvan.div_const (g ^ 2))
      rw [zero_div] at this
      simpa using ENNReal.tendsto_ofReal this
    have h2 : Tendsto (fun k => 1 - ENNReal.ofReal ((⨆ i, μ k i) / g ^ 2)) atTop (𝓝 1) := by
      have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ENNReal))) h1
        (Or.inl ENNReal.one_ne_top)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h2 tendsto_const_nhds hlow hup
  constructor
  · refine squeeze ((∫ y, x y ∂F1) - p) (by linarith) _ (fun k => ?_) (fun k => prob_le_one)
    set P := Measure.pi fun _ : Fin (n k) => F1
    set A := {s : Fin (n k) → S | p < ∑ i, μ k i * x (s i)}
    have hsub : Aᶜ ⊆ {s | (∫ y, x y ∂F1) - p ≤ |∑ i, μ k i * x (s i) - ∫ y, x y ∂F1|} := by
      intro s hs
      simp only [A, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hs
      simp only [Set.mem_setOf_eq]
      rw [abs_sub_comm]
      exact le_trans (by linarith) (le_abs_self _)
    have hc := (measure_mono hsub).trans
      (NL_cheb F1 x hxm hb1 (μ k) (hμ0 k) (hμ1 k) (c := (∫ y, x y ∂F1) - p) (by linarith))
    have hu : (1 : ENNReal) ≤ P A + P Aᶜ := by
      rw [← measure_univ (μ := P), ← Set.union_compl_self A]
      exact measure_union_le _ _
    calc 1 - ENNReal.ofReal ((⨆ i, μ k i) / ((∫ y, x y ∂F1) - p) ^ 2) ≤ 1 - P Aᶜ :=
          tsub_le_tsub_left hc _
      _ ≤ P A := tsub_le_iff_right.2 hu
  · refine squeeze (p - ∫ y, x y ∂F0) (by linarith) _ (fun k => ?_) (fun k => prob_le_one)
    set P := Measure.pi fun _ : Fin (n k) => F0
    set A := {s : Fin (n k) → S | ∑ i, μ k i * x (s i) < p}
    have hsub : Aᶜ ⊆ {s | p - (∫ y, x y ∂F0) ≤ |∑ i, μ k i * x (s i) - ∫ y, x y ∂F0|} := by
      intro s hs
      simp only [A, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hs
      simp only [Set.mem_setOf_eq]
      exact le_trans (by linarith) (le_abs_self _)
    have hc := (measure_mono hsub).trans
      (NL_cheb F0 x hxm hb0 (μ k) (hμ0 k) (hμ1 k) (c := p - ∫ y, x y ∂F0) (by linarith))
    have hu : (1 : ENNReal) ≤ P A + P Aᶜ := by
      rw [← measure_univ (μ := P), ← Set.union_compl_self A]
      exact measure_union_le _ _
    calc 1 - ENNReal.ofReal ((⨆ i, μ k i) / (p - ∫ y, x y ∂F0) ^ 2) ≤ 1 - P Aᶜ :=
          tsub_le_tsub_left hc _
      _ ≤ P A := tsub_le_iff_right.2 hu
