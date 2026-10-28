-- Prove2me | solution 1 for GreedyRS.Tight.ec1_6_liminf_pics
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T10:39:45.032011+00:00
-- url     : https://prove2.me/submissions/82f119fe-2507-42b2-be94-1c84f3567c4f

import Mathlib
import Definitions.Def_GreedyRS_Tight_Setting
import Theorems.Thm_GreedyRS_Tight_ec1_11_liminf_pics
import Theorems.Thm_GreedyRS_Greedy_lemma2_Cfun_strictAnti_continuous
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace G6
open GreedyRS.Greedy

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The row `0` of the array is an independent family. -/
lemma row_indep (P : Measure Ω) (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ)
    (hX : NormalArray P μ v X) : iIndepFun (fun j => X 0 j) P := by
  have := hX.indep.precomp (g := fun j : ℕ => ((0 : ℕ), j)) (fun a b h => by simpa using h)
  exact this

lemma partial_sum_law (P : Measure Ω) [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (X : ℕ → ℕ → Ω → ℝ) (hX : NormalArray P μ v X) (n : ℕ) :
    P.map (∑ j ∈ Finset.range n, X 0 j) = gaussianReal (n * μ 0) (n * v 0) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, CharP.cast_eq_zero, zero_mul,
      gaussianReal_zero_var]
    show P.map (fun _ => (0:ℝ)) = _
    rw [Measure.map_const]; simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hind : IndepFun (∑ j ∈ Finset.range n, X 0 j) (X 0 n) P :=
      (row_indep P μ v X hX).indepFun_finsetSum_of_notMem (fun j => hX.meas 0 j)
        (by simp)
    rw [gaussianReal_add_gaussianReal_of_indepFun hind ih (hX.law 0 n)]
    congr 1
    · push_cast; ring
    · push_cast; ring

lemma runMean_atom (P : Measure Ω) [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (X : ℕ → ℕ → Ω → ℝ) (hX : NormalArray P μ v X) (hv : v 0 ≠ 0) (a : ℝ) (n : ℕ)
    (hn : 1 ≤ n) :
    P {ω | runMean (fun i j => X i j ω) 0 n = a} = 0 := by
  have hmeas : Measurable (∑ j ∈ Finset.range n, X 0 j) := by
    have h := Finset.measurable_sum (Finset.range n) (fun j _ => hX.meas 0 j)
    convert h using 1; ext ω; simp
  have hsub : {ω | runMean (fun i j => X i j ω) 0 n = a} ⊆
      (∑ j ∈ Finset.range n, X 0 j) ⁻¹' {n * a} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, runMean] at hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.sum_apply]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [← hω]; field_simp
  refine measure_mono_null hsub ?_
  rw [← Measure.map_apply hmeas (MeasurableSet.singleton _), partial_sum_law P μ v X hX n]
  have hnv : ((n : ℝ≥0) * v 0) ≠ 0 := by
    refine mul_ne_zero ?_ hv
    exact_mod_cast (show n ≠ 0 by omega)
  exact gaussianReal_absolutelyContinuous _ hnv (by simp)


lemma crossBelow_eq (y : ℕ → ℝ) (b : ℝ) (m : ℕ) (hm : 1 ≤ m) (hym : y m < b)
    (hbefore : ∀ n, 1 ≤ n → n < m → b ≤ y n) : crossBelow y b 1 = (m : ℕ∞) := by
  unfold crossBelow
  apply le_antisymm
  · exact iInf₂_le m ⟨hm, hym⟩
  · refine le_iInf₂ fun n hn => ?_
    have : m ≤ n := not_lt.1 fun h => absurd (hbefore n hn.1 h) (not_le.2 hn.2)
    exact_mod_cast this

lemma levels (C : ℝ → ℝ) (hanti : StrictAntiOn C (Set.Ioi 0)) (hcont : ContinuousOn C (Set.Ioi 0))
    (X x0 : ℝ) (hx0 : 0 < x0) (hX : x0 < X) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < x0)
    (hδ2 : x0 + δ < X) :
    ∃ ε : ℝ, 0 < 2 * ε ∧ 2 * ε < C x0 - C X ∧
      (∃ xm ∈ Set.Ioo x0 (x0 + δ), C xm = C x0 - 2 * ε) ∧
      (∃ xp ∈ Set.Ioo (x0 - δ) x0, C xp = C x0 + 2 * ε) := by
  have hmem : ∀ t, 0 < t → t ∈ Set.Ioi (0 : ℝ) := fun t ht => ht
  have hL : C x0 < C (x0 - δ) := hanti (hmem _ (by linarith)) (hmem _ hx0) (by linarith)
  have hR : C (x0 + δ) < C x0 := hanti (hmem _ hx0) (hmem _ (by linarith)) (by linarith)
  have hXX : C X < C x0 := hanti (hmem _ hx0) (hmem _ (by linarith)) hX
  set ε := min (min (C (x0 - δ) - C x0) (C x0 - C (x0 + δ))) (C x0 - C X) / 4 with hε
  have hεpos : 0 < ε := by
    rw [hε]; apply div_pos _ (by norm_num)
    exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have h1 : ε ≤ (C (x0 - δ) - C x0) / 4 := by
    rw [hε]; apply div_le_div_of_nonneg_right _ (by norm_num)
    exact (min_le_left _ _).trans (min_le_left _ _)
  have h2 : ε ≤ (C x0 - C (x0 + δ)) / 4 := by
    rw [hε]; apply div_le_div_of_nonneg_right _ (by norm_num)
    exact (min_le_left _ _).trans (min_le_right _ _)
  have h3 : ε ≤ (C x0 - C X) / 4 := by
    rw [hε]; apply div_le_div_of_nonneg_right _ (by norm_num)
    exact min_le_right _ _
  refine ⟨ε, by linarith, by linarith, ?_, ?_⟩
  · have hc : ContinuousOn C (Set.Icc x0 (x0 + δ)) :=
      hcont.mono fun t ht => hmem _ (by linarith [ht.1])
    obtain ⟨xm, hxm, hCxm⟩ := intermediate_value_Icc' (by linarith) hc
      (show C x0 - 2 * ε ∈ Set.Icc (C (x0 + δ)) (C x0) from ⟨by linarith, by linarith⟩)
    refine ⟨xm, ⟨lt_of_le_of_ne hxm.1 ?_, lt_of_le_of_ne hxm.2 ?_⟩, hCxm⟩
    · rintro rfl; linarith
    · rintro rfl; linarith
  · have hc : ContinuousOn C (Set.Icc (x0 - δ) x0) :=
      hcont.mono fun t ht => hmem _ (by linarith [ht.1])
    obtain ⟨xp, hxp, hCxp⟩ := intermediate_value_Icc' (by linarith) hc
      (show C x0 + 2 * ε ∈ Set.Icc (C x0) (C (x0 - δ)) from ⟨by linarith, by linarith⟩)
    refine ⟨xp, ⟨lt_of_le_of_ne hxp.1 ?_, lt_of_le_of_ne hxp.2 ?_⟩, hCxp⟩
    · rintro rfl; linarith
    · rintro rfl; linarith

end G6

open GreedyRS.Greedy in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ) (hX : GreedyRS.Greedy.NormalArray P μ v X)
    (γ : ℝ) (hγ : 0 < γ) (hslip : ∀ i, 1 ≤ i → μ i = μ 0 - γ)
    (w : ℝ≥0) (hw : 0 < w) (hcv : ∀ i, v i = w)
    (c : ℝ) (hc : GreedyRS.Greedy.Cfun (γ / Real.sqrt w) < c)
    (γ0 : ℝ) (hγ0 : γ0 ∈ Set.Ioo 0 γ) (hC0 : GreedyRS.Greedy.Cfun ((γ - γ0) / Real.sqrt w) = c) :
    P {ω | ∃ n : ℕ, 1 ≤ n ∧ GreedyRS.Greedy.runMean (fun i j => X i j ω) 0 n < μ 0 - γ0}
      ≤ Filter.liminf
          (fun k : ℕ => P {ω | GreedyRS.Greedy.greedySelect k ⌊c * k⌋₊ (fun i j => X i j ω) ≠ 0}) atTop := by
  obtain ⟨hanti, hcont⟩ := GreedyRS.Greedy.lemma2_Cfun_strictAnti_continuous
  set σ := Real.sqrt w with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 (by exact_mod_cast hw)
  set x0 := (γ - γ0) / σ with hx0def
  set XX := γ / σ with hXXdef
  have hx0 : 0 < x0 := div_pos (by linarith [hγ0.2]) hσ
  have hx0X : x0 < XX := div_lt_div_of_pos_right (by linarith [hγ0.1]) hσ
  set δ0 := min x0 (XX - x0) / 2 with hδ0
  have hδ0pos : 0 < δ0 := by rw [hδ0]; exact div_pos (lt_min hx0 (by linarith)) (by norm_num)
  have hδ0a : δ0 < x0 := by
    have := min_le_left x0 (XX - x0); rw [hδ0]; linarith
  have hδ0b : x0 + δ0 < XX := by
    have := min_le_right x0 (XX - x0); rw [hδ0]; linarith
  set d : ℕ → ℝ := fun j => δ0 / ((j : ℝ) + 1) with hd
  have hdpos : ∀ j, 0 < d j := fun j => div_pos hδ0pos (by positivity)
  have hdle : ∀ j, d j ≤ δ0 := fun j => div_le_self hδ0pos.le (by have := (Nat.cast_nonneg j : (0:ℝ) ≤ j); linarith)
  have hlev : ∀ j : ℕ, ∃ ε γm γp : ℝ,
      (0 < 2 * ε ∧ 2 * ε < c - Cfun (γ / σ)) ∧ γm ∈ Set.Ioo 0 γ ∧ γp ∈ Set.Ioo 0 γ ∧
      Cfun ((γ - γm) / σ) = c - 2 * ε ∧ Cfun ((γ - γp) / σ) = c + 2 * ε ∧
      γ0 - σ * d j < γm ∧ γm < γ0 ∧ γ0 < γp ∧ γp < γ0 + σ * d j := by
    intro j
    obtain ⟨ε, hε1, hε2, ⟨xm, hxm, hCm⟩, ⟨xp, hxp, hCp⟩⟩ :=
      G6.levels Cfun hanti hcont XX x0 hx0 hx0X (d j) (hdpos j)
        (lt_of_le_of_lt (hdle j) hδ0a) (by linarith [hdle j])
    have hγx : ∀ t, (γ - (γ - σ * t)) / σ = t := fun t => by field_simp; ring
    have hγ0x : γ0 = γ - σ * x0 := by rw [hx0def]; field_simp; ring
    have hγX : γ = σ * XX := by rw [hXXdef]; field_simp
    refine ⟨ε, γ - σ * xm, γ - σ * xp, ⟨hε1, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hC0]; exact hε2
    · have : xm < XX := by linarith [hxm.2, hdle j]
      nlinarith
    · nlinarith [hxm.1]
    · have : xp < XX := by linarith [hxp.2]
      nlinarith
    · have : 0 < xp := by linarith [hxp.1, hdle j]
      nlinarith
    · rw [hγx, hCm, hC0]
    · rw [hγx, hCp, hC0]
    · rw [hγ0x]; nlinarith [hxm.2]
    · rw [hγ0x]; nlinarith [hxm.1]
    · rw [hγ0x]; nlinarith [hxp.2]
    · rw [hγ0x]; nlinarith [hxp.1]
  choose ε γm γp hj using hlev
  set y : Ω → ℕ → ℝ := fun ω => runMean (fun i j => X i j ω) 0 with hy
  set a := μ 0 - γ0 with ha
  set A : ℕ → Set Ω := fun j => {ω | ∃ m : ℕ, crossBelow (y ω) (μ 0 - γp j) 1 = m ∧
      ∀ n ∈ Finset.Icc 1 (m - 1), μ 0 - γm j ≤ y ω n} with hA
  set L := Filter.liminf
    (fun k : ℕ => P {ω | greedySelect k ⌊c * k⌋₊ (fun i j => X i j ω) ≠ 0}) atTop with hL
  have hAL : ∀ j, P (A j) ≤ L := fun j =>
    GreedyRS.Tight.ec1_11_liminf_pics P μ v X hX γ hγ hslip w hw hcv c hc (ε j) (hj j).1
      (γm j) (γp j) (hj j).2.1 (hj j).2.2.1 (hj j).2.2.2.1 (hj j).2.2.2.2.1
  set B : ℕ → Set Ω := fun J => ⋂ j, ⋂ (_ : J ≤ j), A j with hB
  have hBmono : Monotone B := by
    intro J J' hJJ' ω hω
    simp only [hB, Set.mem_iInter] at hω ⊢
    exact fun j hj' => hω j (hJJ'.trans hj')
  set N : Set Ω := ⋃ n : ℕ, ({ω | 1 ≤ n} ∩ {ω | y ω n = a}) with hN
  have hv0 : v 0 ≠ 0 := by rw [hcv 0]; exact hw.ne'
  have hNnull : P N = 0 := by
    refine measure_iUnion_null fun n => ?_
    by_cases hn : 1 ≤ n
    · exact measure_mono_null Set.inter_subset_right (G6.runMean_atom P μ v X hX hv0 a n hn)
    · have : {ω : Ω | 1 ≤ n} = ∅ := by ext; simp [hn]
      rw [this, Set.empty_inter, measure_empty]
  have hdlim : ∀ t, 0 < t → ∀ᶠ j in atTop, σ * d j < t := by
    intro t ht
    have h0 : Tendsto (fun j : ℕ => σ * d j) atTop (𝓝 0) := by
      have : Tendsto (fun j : ℕ => δ0 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat δ0 |>.comp (tendsto_add_atTop_nat 1) |>.congr
          (fun j => by simp)
      simpa using this.const_mul σ
    exact h0.eventually (gt_mem_nhds ht)
  have hsub : {ω | ∃ n : ℕ, 1 ≤ n ∧ y ω n < a} ⊆ N ∪ ⋃ J, B J := by
    intro ω hω
    by_cases hωN : ω ∈ N
    · exact Or.inl hωN
    right
    classical
    let m := Nat.find hω
    have hm : 1 ≤ m ∧ y ω m < a := Nat.find_spec hω
    have hmin : ∀ n, 1 ≤ n → n < m → a ≤ y ω n := by
      intro n hn hnm
      by_contra hlt
      exact Nat.find_min hω hnm ⟨hn, not_le.1 hlt⟩
    have hgt : ∀ n, 1 ≤ n → n < m → a < y ω n := by
      intro n hn hnm
      refine lt_of_le_of_ne (hmin n hn hnm) fun heq => hωN ?_
      exact Set.mem_iUnion.2 ⟨n, hn, heq.symm⟩
    have hev1 : ∀ᶠ j in atTop, σ * d j < a - y ω m := hdlim _ (by linarith [hm.2])
    have hev2 : ∀ᶠ j in atTop, ∀ n ∈ Finset.Icc 1 (m - 1), σ * d j < y ω n - a := by
      rw [Filter.eventually_all_finset]
      intro n hn
      rw [Finset.mem_Icc] at hn
      exact hdlim _ (by linarith [hgt n hn.1 (by omega)])
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (hev1.and hev2)
    refine Set.mem_iUnion.2 ⟨J, ?_⟩
    simp only [hB, Set.mem_iInter]
    intro j hjJ
    obtain ⟨h1, h2⟩ := hJ j hjJ
    obtain ⟨-, -, -, -, -, hm1, hm2, hp1, hp2⟩ := hj j
    refine ⟨m, ?_, ?_⟩
    · apply G6.crossBelow_eq _ _ _ hm.1
      · linarith
      · intro n hn hnm; linarith [hmin n hn hnm]
    · intro n hn
      have hn' := Finset.mem_Icc.1 hn
      have := h2 n hn
      linarith
  calc P {ω | ∃ n : ℕ, 1 ≤ n ∧ y ω n < a} ≤ P (N ∪ ⋃ J, B J) := measure_mono hsub
    _ ≤ P N + P (⋃ J, B J) := measure_union_le _ _
    _ = P (⋃ J, B J) := by rw [hNnull, zero_add]
    _ = ⨆ J, P (B J) := hBmono.measure_iUnion
    _ ≤ L := iSup_le fun J => (measure_mono (by
          intro ω hω
          simp only [hB, Set.mem_iInter] at hω
          exact hω J le_rfl)).trans (hAL J)
