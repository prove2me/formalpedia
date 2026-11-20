-- Prove2me | solution 1 for LevyStochCalc.Poisson.ae_count_time_singleton_le_one
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T14:27:03.358246+00:00
-- url     : https://prove2.me/submissions/4eeaedc5-041e-44fa-a69d-c9c69edeac9d

import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F000
import Definitions.Def_LevyStochCalc_Poisson_ZeroIntensity_F000
import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F002

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open LevyStochCalc.Poisson

lemma timeSlab_disjoint (n : ℕ) : Pairwise (fun k l : ℕ => Disjoint (timeSlab n k) (timeSlab n l)) := by
  intro k l hkl
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [timeSlab, Set.mem_Ioc] at hx hx'
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_lt_iff₀ h2, le_div_iff₀ h2] at hx hx'
  have a1 : (k : ℝ) < l + 1 := by linarith [hx.1, hx'.2]
  have a2 : (l : ℝ) < k + 1 := by linarith [hx'.1, hx.2]
  have b1 : k < l + 1 := by exact_mod_cast a1
  have b2 : l < k + 1 := by exact_mod_cast a2
  omega

theorem slab_le_one {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) :
    ∀ᵐ ω ∂P, ∃ n : ℕ, ∀ k : ℕ, N.N ω (B ∩ timeSlab n k ×ˢ Set.univ) ≤ 1 := by
  set Bk : ℕ → ℕ → Set (ℝ × E) := fun n k => B ∩ timeSlab n k ×ˢ Set.univ with hBk
  have hBkm : ∀ n k, MeasurableSet (Bk n k) := fun n k =>
    hB.inter ((measurableSet_timeSlab n k).prod MeasurableSet.univ)
  have hBkle : ∀ n k, referenceIntensity ν (Bk n k) ≤ referenceIntensity ν B :=
    fun n k => measure_mono Set.inter_subset_left
  have hBkfin : ∀ n k, referenceIntensity ν (Bk n k) ≠ ⊤ :=
    fun n k => ne_top_of_le_ne_top hfin (hBkle n k)
  -- sum of slab intensities
  have hsum : ∀ n, ∑' k, referenceIntensity ν (Bk n k) ≤ referenceIntensity ν B := by
    intro n
    refine (tsum_meas_le_meas_iUnion_of_disjoint _ (fun k => hBkm n k) ?_).trans ?_
    · intro k l hkl
      rw [Function.onFun, Set.disjoint_left]
      intro x hx hx'
      exact Set.disjoint_left.mp (timeSlab_disjoint n hkl) hx.2.1 hx'.2.1
    · exact measure_mono (Set.iUnion_subset fun k => Set.inter_subset_left)
  -- the bad event at level n
  set bad : ℕ → Set Ω := fun n => {ω | ∃ k, 2 ≤ N.N ω (Bk n k)} with hbad
  have hbad_le : ∀ (ε : ℝ≥0∞), ε ≠ 0 → ∃ n, P (bad n) ≤ ε * referenceIntensity ν B := by
    intro ε hε
    have hg : ∫⁻ x, sectionDensity ν B x ≠ ⊤ := by rw [lintegral_sectionDensity hB]; exact hfin
    obtain ⟨δ, hδ, hsmall⟩ := exists_pos_setLIntegral_lt_of_measure_lt hg hε
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) < δ := by
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt hδ.ne'
      refine ⟨n, lt_of_le_of_lt (le_of_eq ?_) hn⟩
      rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    have hslab : ∀ k, referenceIntensity ν (Bk n k) ≤ ε := by
      intro k
      rw [hBk, Prove2MeSourceProof.h_b53022bf4ec47748c83ffa9f hB (measurableSet_timeSlab n k)]
      refine (hsmall _ ?_).le
      rw [volume_timeSlab]; exact hn
    refine ⟨n, ?_⟩
    calc P (bad n) = P (⋃ k, {ω | 2 ≤ N.N ω (Bk n k)}) := by
          congr 1; ext ω; simp [hbad]
      _ ≤ ∑' k, P {ω | 2 ≤ N.N ω (Bk n k)} := measure_iUnion_le _
      _ ≤ ∑' k, referenceIntensity ν (Bk n k) ^ 2 :=
          ENNReal.tsum_le_tsum (fun k => measure_two_le_count_le N (hBkm n k) (hBkfin n k))
      _ ≤ ∑' k, ε * referenceIntensity ν (Bk n k) := by
          refine ENNReal.tsum_le_tsum (fun k => ?_)
          rw [sq]; gcongr; exact hslab k
      _ = ε * ∑' k, referenceIntensity ν (Bk n k) := ENNReal.tsum_mul_left
      _ ≤ ε * referenceIntensity ν B := by gcongr; exact hsum n
  have hnull : P (⋂ n, bad n) = 0 := by
    have hle : ∀ j : ℕ, P (⋂ n, bad n) ≤ (j : ℝ≥0∞)⁻¹ * referenceIntensity ν B := by
      intro j
      obtain ⟨n, hn⟩ := hbad_le ((j : ℝ≥0∞)⁻¹) (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top j))
      exact (measure_mono (Set.iInter_subset _ n)).trans hn
    have ht : Tendsto (fun j : ℕ => (j : ℝ≥0∞)⁻¹ * referenceIntensity ν B) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hfin)
      simpa using this
    exact le_antisymm (ge_of_tendsto' ht hle) bot_le
  have hint : ∀ᵐ ω ∂P, ∀ n k, ∃ m : ℕ, N.N ω (Bk n k) = m :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun k => N.integer_valued (hBkm n k) (hBkfin n k)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull, hint] with ω h1 h2
  simp only [Set.mem_iInter, hbad, Set.mem_setOf_eq, not_forall, not_exists] at h1
  obtain ⟨n, hn⟩ := h1
  refine ⟨n, fun k => ?_⟩
  obtain ⟨m, hm⟩ := h2 n k
  have := hn k
  rw [hm] at this ⊢
  have : m < 2 := by exact_mod_cast not_le.mp this
  exact_mod_cast (by omega : m ≤ 1)

theorem solution {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, N.N ω (B ∩ {s} ×ˢ Set.univ) ≤ 1 := by
  filter_upwards [slab_le_one N hB hfin, ae_count_Iic_zero_eq_zero N hB] with ω h1 h0 s
  rcases le_or_gt s 0 with hs | hs
  · calc N.N ω (B ∩ {s} ×ˢ Set.univ) ≤ N.N ω (B ∩ Set.Iic (0 : ℝ) ×ˢ Set.univ) := by
          refine measure_mono (Set.inter_subset_inter_right _ (Set.prod_mono ?_ le_rfl))
          intro x hx; rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hs
      _ = 0 := h0
      _ ≤ 1 := zero_le_one
  · obtain ⟨n, hn⟩ := h1
    have hpos : 0 < s * 2 ^ n := by positivity
    have hc1 : 1 ≤ ⌈s * 2 ^ n⌉₊ := Nat.one_le_iff_ne_zero.mpr
      (by rw [Ne, Nat.ceil_eq_zero, not_le]; exact hpos)
    set k := ⌈s * 2 ^ n⌉₊ - 1 with hk
    have hk1 : k + 1 = ⌈s * 2 ^ n⌉₊ := Nat.sub_add_cancel hc1
    have hlt : (k : ℝ) < s * 2 ^ n := by
      have h := Nat.ceil_lt_add_one hpos.le
      have : ((k + 1 : ℕ) : ℝ) < s * 2 ^ n + 1 := by rw [hk1]; exact h
      push_cast at this; linarith
    have hge : s * 2 ^ n ≤ (k : ℝ) + 1 := by
      have h := Nat.le_ceil (s * 2 ^ n)
      rw [← hk1] at h; push_cast at h; exact h
    have hmem : s ∈ timeSlab n k := by
      have h2 : (0 : ℝ) < 2 ^ n := by positivity
      simp only [timeSlab, Set.mem_Ioc]
      rw [div_lt_iff₀ h2, le_div_iff₀ h2]; exact ⟨hlt, hge⟩
    refine le_trans (measure_mono ?_) (hn k)
    refine Set.inter_subset_inter_right _ (Set.prod_mono ?_ le_rfl)
    intro x hx; rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hmem
