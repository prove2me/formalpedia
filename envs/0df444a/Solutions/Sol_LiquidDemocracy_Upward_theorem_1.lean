-- Prove2me | solution 1 for LiquidDemocracy.Upward.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T11:13:21.117521+00:00
-- url     : https://prove2.me/submissions/5a1ad57b-545b-4ddc-a601-be25483fb64f

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Setting
import Definitions.Def_LiquidDemocracy_Upward_Urn
import Theorems.Thm_LiquidDemocracy_Upward_lemma_1
import Theorems.Thm_LiquidDemocracy_Upward_lemma_2
import Theorems.Thm_LiquidDemocracy_Upward_urn_coupling
import Theorems.Thm_LiquidDemocracy_Upward_upward_cond_2
import Theorems.Thm_LiquidDemocracy_Upward_upward_cond_3

open MeasureTheory Filter Topology Asymptotics LiquidDemocracy.Upward

/-- Under `instanceLaw`, a.e. every competence is nonnegative. -/
theorem LD_aux_neg_null (D : Measure ℝ) (hD : D ∈ ContClass) (M : Model) (n : ℕ) :
    instanceLaw D M n {ω | ∃ i, ω.1 i < 0} = 0 := by
  obtain ⟨hP, hS, -⟩ := hD
  have hpi : (Measure.pi fun _ : Fin n => D) {c : Fin n → ℝ | ∃ i, c i < 0} = 0 := by
    have : {c : Fin n → ℝ | ∃ i, c i < 0} = ⋃ i, (Function.eval i) ⁻¹' Set.Iio 0 := by
      ext c; simp
    rw [this, measure_iUnion_null_iff]
    intro i
    apply Measure.pi_eval_preimage_null
    apply measure_mono_null _ hS
    intro x hx
    simp only [Set.mem_Iio] at hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and, not_le]
    intro h; linarith
  unfold instanceLaw
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro g _
  have hmeas : MeasurableSet {ω : (Fin n → ℝ) × DelegGraph n | ∃ i, ω.1 i < 0} := by
    have : {ω : (Fin n → ℝ) × DelegGraph n | ∃ i, ω.1 i < 0} = ⋃ i, {ω | ω.1 i < 0} := by
      ext; simp
    rw [this]
    exact MeasurableSet.iUnion fun i =>
      measurableSet_lt ((measurable_pi_apply i).comp measurable_fst) measurable_const
  rw [Measure.map_apply (by fun_prop) hmeas]
  apply withDensity_absolutelyContinuous
  exact hpi

theorem solution (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ProbDNH (upward p) ContClass ∧ ProbPG (upward p) ContClass := by
  have hcls : ∀ D ∈ ContClass, IsProbabilityMeasure D ∧ D (Set.Icc 0 1)ᶜ = 0 :=
    fun D hD => ⟨hD.1, hD.2.1⟩
  have hq : ∀ x ∈ Set.Icc (0 : ℝ) 1, (upward p).q x ∈ Set.Icc (0 : ℝ) 1 :=
    fun _ _ => ⟨hp.1.le, hp.2.le⟩
  have hφ : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (upward p).φ x y := by
    intro x _ y _
    simp only [upward]
    split_ifs <;> norm_num
  have hqm : Measurable (upward p).q := measurable_const
  have hφm : Measurable (Function.uncurry (upward p).φ) := by
    simp only [upward]
    change Measurable fun z : ℝ × ℝ => if z.1 < z.2 then (1 : ℝ) else 0
    exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      measurable_const measurable_const
  obtain ⟨δ, hδ1, hL⟩ := lemma_2 p hp
  have h12 : ∀ D ∈ ContClass, ∃ α ∈ Set.Ioo (0 : ℝ) 1, ∃ C : ℕ → ℕ,
      (fun n => (C n : ℝ)) =o[atTop] (fun n => (n : ℝ)) ∧
      Tendsto (fun n => (instanceLaw D (upward p) n).real {ω | maxWeight ω.2 ≤ C n})
        atTop (𝓝 1) ∧
      Tendsto (fun n => (instanceLaw D (upward p) n).real
        {ω | 2 * α * n ≤ ∑ i, (weight ω.2 i : ℝ) * ω.1 i - ∑ i, ω.1 i}) atTop (𝓝 1) := by
    intro D hD
    obtain ⟨α, hα, h2⟩ := upward_cond_2 p hp D hD
    refine ⟨α, hα, fun n => ⌊(n : ℝ) ^ δ⌋₊, ?_, ?_, h2⟩
    · -- `⌊n^δ⌋₊ = o(n)` since `δ < 1`
      set δ' := max δ 0 with hδ'
      have hδ'1 : δ' < 1 := max_lt hδ1 one_pos
      have hbig' : (fun n : ℕ => (n : ℝ) ^ δ') =o[atTop] (fun n : ℕ => (n : ℝ)) := by
        rw [isLittleO_iff_tendsto']
        · have ht : Tendsto (fun x : ℝ => x ^ (-(1 - δ'))) atTop (𝓝 0) :=
            tendsto_rpow_neg_atTop (by linarith)
          refine (ht.comp tendsto_natCast_atTop_atTop).congr' ?_
          filter_upwards [eventually_ge_atTop 1] with n hn
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
          simp only [Function.comp_apply]
          rw [show -(1 - δ') = δ' - 1 by ring, Real.rpow_sub_one hn0.ne']
        · filter_upwards [eventually_ge_atTop 1] with n hn h
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
          exact absurd h hn0.ne'
      refine IsBigO.trans_isLittleO ?_ hbig'
      apply IsBigO.of_bound 1
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
      calc (⌊(n : ℝ) ^ δ⌋₊ : ℝ) ≤ (n : ℝ) ^ δ := Nat.floor_le (by positivity)
        _ ≤ (n : ℝ) ^ δ' := Real.rpow_le_rpow_of_exponent_le hn' (le_max_left _ _)
    · refine hL.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [(urn_coupling p hp D hD n hn).2]
      congr 1
      ext s
      simp only [Set.mem_setOf_eq]
      rw [Nat.le_floor_iff (by positivity)]
  have hL1 := lemma_1 (upward p) ContClass hcls hq hφ hqm hφm h12
  refine ⟨hL1.1, hL1.2 ?_⟩
  obtain ⟨D, hD, α, hα, h3⟩ := upward_cond_3 p hp
  refine ⟨D, hD, α, ⟨hα, ?_⟩, h3⟩
  by_contra hge
  push Not at hge
  have hzero : ∀ n ≥ 1, (instanceLaw D (upward p) n).real
      {ω | ∑ i, ω.1 i + α * n ≤ (n : ℝ) / 2 ∧
        (n : ℝ) / 2 ≤ ∑ i, (weight ω.2 i : ℝ) * ω.1 i - α * n} = 0 := by
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [measureReal_def, measure_mono_null _ (LD_aux_neg_null D hD (upward p) n),
      ENNReal.toReal_zero]
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    by_contra hall
    push Not at hall
    have : 0 ≤ ∑ i, ω.1 i := Finset.sum_nonneg fun i _ => hall i
    nlinarith [hω.1]
  have h0 : Tendsto (fun n => (instanceLaw D (upward p) n).real
      {ω | ∑ i, ω.1 i + α * n ≤ (n : ℝ) / 2 ∧
        (n : ℝ) / 2 ≤ ∑ i, (weight ω.2 i : ℝ) * ω.1 i - α * n}) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hzero n hn).symm
  have := tendsto_nhds_unique h3 h0
  norm_num at this
