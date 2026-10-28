-- Prove2me | solution 1 for GreedyRS.EFG.theorem3_efg_sample_optimality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T10:36:16.8795+00:00
-- url     : https://prove2.me/submissions/f2174ce1-833c-4233-a0a4-ff79029d1ebf

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting
import Theorems.Thm_GreedyRS_EFG_lemma4_crossing_time
import Theorems.Thm_GreedyRS_EFG_lemma7_C_continuous_antitone
import Theorems.Thm_GreedyRS_EFG_theorem3_liminf_at_level

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace GRSHelp
open GreedyRS.Greedy

lemma crossTime_le {x : ℝ} {n0 n : ℕ} {z : ℕ → ℝ} (h1 : n0 ≤ n) (h2 : zbar z n < x) :
    crossTime x n0 z ≤ n := iInf₂_le n ⟨h1, h2⟩

lemma le_crossTime {x : ℝ} {n0 : ℕ} {z : ℕ → ℝ} {m : ℕ∞}
    (h : ∀ n, n0 ≤ n → zbar z n < x → m ≤ n) : m ≤ crossTime x n0 z :=
  le_iInf₂ fun n hn => h n hn.1 hn.2

lemma crossTime_anti {x y : ℝ} (hxy : x ≤ y) (n0 : ℕ) (z : ℕ → ℝ) :
    crossTime y n0 z ≤ crossTime x n0 z :=
  le_crossTime fun _ h1 h2 => crossTime_le h1 (h2.trans_le hxy)

lemma crossTime_spec {x : ℝ} {n0 : ℕ} {z : ℕ → ℝ} (h : crossTime x n0 z < ⊤) :
    ∃ n : ℕ, crossTime x n0 z = n ∧ n0 ≤ n ∧ zbar z n < x := by
  have hne : ({n | n0 ≤ n ∧ zbar z n < x} : Set ℕ).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    apply h.ne
    apply le_antisymm le_top
    apply le_crossTime
    intro n h1 h2
    have : n ∈ ({n | n0 ≤ n ∧ zbar z n < x} : Set ℕ) := ⟨h1, h2⟩
    rw [hne] at this; exact this.elim
  refine ⟨sInf {n | n0 ≤ n ∧ zbar z n < x}, ?_, Nat.sInf_mem hne⟩
  rw [ENat.natCast_sInf hne]
  rfl

lemma measurable_zbar (n : ℕ) : Measurable (fun z : ℕ → ℝ => zbar z n) := by
  unfold zbar
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun j _ => measurable_pi_apply j)

lemma measurable_crossTime_enn (x : ℝ) (n0 : ℕ) :
    Measurable (fun z => ((crossTime x n0 z : ℕ∞) : ℝ≥0∞)) := by
  have : (fun z => ((crossTime x n0 z : ℕ∞) : ℝ≥0∞)) =
      fun z => ⨅ n : ℕ, (if n0 ≤ n ∧ zbar z n < x then (n : ℝ≥0∞) else ⊤) := by
    funext z
    unfold crossTime
    rw [ENat.toENNReal_iInf]
    congr 1; funext n
    rw [ENat.toENNReal_iInf]
    by_cases h : n0 ≤ n ∧ zbar z n < x
    · simp [h]
    · simp [h]
  rw [this]
  apply Measurable.iInf
  intro n
  apply Measurable.ite _ measurable_const measurable_const
  by_cases hn : n0 ≤ n
  · simp only [hn, true_and]
    exact measurableSet_lt (measurable_zbar n) measurable_const
  · simp [hn]

lemma measurable_crossTime (x : ℝ) (n0 : ℕ) : Measurable (crossTime x n0) := by
  apply measurable_to_countable'
  intro m
  have : crossTime x n0 ⁻¹' {m} = (fun z => ((crossTime x n0 z : ℕ∞) : ℝ≥0∞)) ⁻¹' {(m : ℝ≥0∞)} := by
    ext z; simp
  rw [this]
  exact measurable_crossTime_enn x n0 (measurableSet_singleton _)

instance : IsProbabilityMeasure stdNormalSeq := by
  unfold stdNormalSeq; infer_instance

lemma iIndep_coord : iIndepFun (fun (i : ℕ) (z : ℕ → ℝ) => z i) stdNormalSeq := by
  unfold stdNormalSeq
  exact iIndepFun_infinitePi (X := fun _ ω => ω) (fun _ => measurable_id)

lemma map_coord (i : ℕ) : stdNormalSeq.map (fun z : ℕ → ℝ => z i) = gaussianReal 0 1 := by
  unfold stdNormalSeq
  exact Measure.infinitePi_map_eval _ i

lemma map_partialSum (n : ℕ) :
    stdNormalSeq.map (fun z : ℕ → ℝ => ∑ j ∈ Finset.range n, z j) = gaussianReal 0 (n : ℝ≥0) := by
  induction n with
  | zero =>
    simp [gaussianReal_zero_var]
  | succ n ih =>
    have hind : IndepFun (∑ j ∈ Finset.range n, (fun (z : ℕ → ℝ) => z j)) (fun z : ℕ → ℝ => z n)
        stdNormalSeq :=
      iIndep_coord.indepFun_finsetSum_of_notMem (fun i => measurable_pi_apply i)
        (by simp)
    have hfun : (fun z : ℕ → ℝ => ∑ j ∈ Finset.range (n + 1), z j) =
        (∑ j ∈ Finset.range n, (fun (z : ℕ → ℝ) => z j)) + (fun z : ℕ → ℝ => z n) := by
      funext z; simp [Finset.sum_range_succ]
    have h1 : stdNormalSeq.map (∑ j ∈ Finset.range n, (fun (z : ℕ → ℝ) => z j)) =
        gaussianReal 0 (n : ℝ≥0) := by
      have : (∑ j ∈ Finset.range n, (fun (z : ℕ → ℝ) => z j)) =
          (fun z : ℕ → ℝ => ∑ j ∈ Finset.range n, z j) := by funext z; simp
      rw [this, ih]
    rw [hfun, gaussianReal_add_gaussianReal_of_indepFun hind h1 (map_coord n)]
    simp

lemma map_zbar_null (n : ℕ) (hn : 1 ≤ n) (a : ℝ) : stdNormalSeq {z | zbar z n = a} = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hset : {z : ℕ → ℝ | zbar z n = a} =
      (fun z : ℕ → ℝ => ∑ j ∈ Finset.range n, z j) ⁻¹' {n * a} := by
    ext z; simp only [zbar, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; rw [← h]; field_simp
    · intro h; rw [h]; field_simp
  rw [hset, ← Measure.map_apply (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))
    (measurableSet_singleton _), map_partialSum]
  have hv : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  exact gaussianReal_absolutelyContinuous 0 hv (Real.volume_singleton)

lemma zbar_Ico_pos (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (hab : a < b) :
    0 < stdNormalSeq {z | a ≤ zbar z n ∧ zbar z n < b} := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hset : {z : ℕ → ℝ | a ≤ zbar z n ∧ zbar z n < b} =
      (fun z : ℕ → ℝ => ∑ j ∈ Finset.range n, z j) ⁻¹' Set.Ico (n * a) (n * b) := by
    ext z; simp only [zbar, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ico]
    rw [le_div_iff₀ hn', div_lt_iff₀ hn']
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hset, ← Measure.map_apply (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))
    measurableSet_Ico, map_partialSum]
  have hv : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [pos_iff_ne_zero]
  intro h0
  have h1 := gaussianReal_absolutelyContinuous' 0 hv h0
  rw [Real.volume_Ico, ENNReal.ofReal_eq_zero] at h1
  nlinarith

lemma iSup_C_right (n0 : ℕ) (hn0 : 1 ≤ n0) (x0 : ℝ) :
    ⨆ m : ℕ, Cn0 (x0 + 1 / ((m : ℝ) + 1)) n0 = Cn0 x0 n0 := by
  unfold Cn0
  have hmono : Monotone (fun (m : ℕ) (z : ℕ → ℝ) =>
      ((crossTime (x0 + 1 / ((m : ℝ) + 1)) n0 z : ℕ∞) : ℝ≥0∞)) := by
    intro m m' hmm z
    apply ENat.toENNReal_le.mpr
    apply crossTime_anti
    have : (1 : ℝ) / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmm 1)
    linarith
  rw [← lintegral_iSup (fun m => measurable_crossTime_enn _ n0) hmono]
  apply lintegral_congr_ae
  have hae : ∀ᵐ z ∂stdNormalSeq, ∀ n : ℕ, zbar z (n + 1) ≠ x0 := by
    rw [ae_all_iff]
    intro n
    have := map_zbar_null (n + 1) (by omega) x0
    rw [measure_eq_zero_iff_ae_notMem] at this
    exact this
  filter_upwards [hae] with z hz
  rw [← ENat.toENNReal_iSup]
  congr 1
  apply le_antisymm
  · exact iSup_le fun m => crossTime_anti (le_add_of_nonneg_right (by positivity)) n0 z
  · -- crossTime x0 ≤ ⨆ T_m
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (⨆ m : ℕ, crossTime (x0 + 1 / ((m : ℝ) + 1)) n0 z) = N :=
      ENat.ne_top_iff_exists.mp (ne_top_of_lt hcon) |>.imp fun _ h => h.symm
    have hNlt : (N : ℕ∞) < crossTime x0 n0 z := hN ▸ hcon
    -- every n ∈ [n0, N] has zbar n > x0
    have hgt : ∀ n, n0 ≤ n → n ≤ N → x0 < zbar z n := by
      intro n h1 h2
      rcases lt_trichotomy (zbar z n) x0 with h | h | h
      · have := crossTime_le h1 h
        have : (N : ℕ∞) < n := lt_of_lt_of_le hNlt this
        exact absurd (by exact_mod_cast this : N < n) (not_lt.mpr h2)
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        exact absurd h (hz k)
      · exact h
    classical
    let mm : ℕ → ℕ := fun n =>
      if h : x0 < zbar z n then Classical.choose (exists_nat_one_div_lt (sub_pos.mpr h)) else 0
    let M := (Finset.range (N + 1)).sup mm
    have hM : (N : ℕ∞) < crossTime (x0 + 1 / ((M : ℝ) + 1)) n0 z := by
      refine lt_of_lt_of_le ?_ (le_crossTime (m := ((N + 1 : ℕ) : ℕ∞)) ?_)
      · exact_mod_cast Nat.lt_succ_self N
      intro n h1 h2
      by_contra hcon2
      have hnN : n ≤ N := by
        by_contra h3; exact hcon2 (by exact_mod_cast (show N + 1 ≤ n by omega))
      have hx := hgt n h1 hnN
      have hmm : mm n ≤ M := Finset.le_sup (f := mm) (Finset.mem_range.mpr (by omega))
      have hspec : 1 / ((mm n : ℝ) + 1) < zbar z n - x0 := by
        simp only [mm, dif_pos hx]
        exact Classical.choose_spec (exists_nat_one_div_lt (sub_pos.mpr hx))
      have : (1 : ℝ) / ((M : ℝ) + 1) ≤ 1 / ((mm n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmm 1)
      linarith
    have := le_iSup (fun m : ℕ => crossTime (x0 + 1 / ((m : ℝ) + 1)) n0 z) M
    rw [hN] at this
    exact absurd (lt_of_lt_of_le hM this) (lt_irrefl _)

end GRSHelp

open GreedyRS.Greedy GRSHelp in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ)
    (hX : GreedyRS.Greedy.NormalArray P μ v X) (hv : ∀ i, 0 < v i)
    (γ σbar : ℝ) (hγ : 0 < γ) (hσbar : 0 < σbar)
    (hgap : ∀ i, 1 ≤ i → μ i ≤ μ 0 - γ) (hvar : ∀ i, (v i : ℝ) ≤ σbar ^ 2)
    (n0 : ℕ) (hn0 : 1 ≤ n0) (ng : ℝ)
    (hng : GreedyRS.Greedy.Cn0 (γ / σbar) n0 < ENNReal.ofReal (n0 + ng)) :
    (∃ γ0 ∈ Set.Ioo 0 γ, GreedyRS.Greedy.Cn0 ((γ - γ0) / σbar) n0 = ENNReal.ofReal (n0 + ng)) ∧
    ∀ γ0 ∈ Set.Ioo 0 γ, GreedyRS.Greedy.Cn0 ((γ - γ0) / σbar) n0 = ENNReal.ofReal (n0 + ng) →
      P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) n0 (μ 0 - γ0)} ≤
        Filter.liminf (fun k : ℕ => GreedyRS.Greedy.pcs P X k n0 ⌊((n0 : ℝ) + ng) * k⌋₊) Filter.atTop := by
  obtain ⟨hstrict, hcont⟩ := GreedyRS.EFG.lemma7_C_continuous_antitone n0 hn0
  have hantiOn := hstrict.antitoneOn
  have hpos : (0 : ℝ) < γ / σbar := div_pos hγ hσbar
  refine ⟨?_, ?_⟩
  · -- existence of the level γ0 (intermediate value theorem)
    have hC0 : Cn0 0 n0 = ⊤ := (GreedyRS.EFG.lemma4_crossing_time n0 hn0).2.2.2
    have hsup := iSup_C_right n0 hn0 0
    simp only [zero_add] at hsup
    rw [hC0] at hsup
    have hlt : ENNReal.ofReal (n0 + ng) < ⨆ m : ℕ, Cn0 (1 / ((m : ℝ) + 1)) n0 := by
      rw [hsup]; exact ENNReal.ofReal_lt_top
    obtain ⟨m, hm⟩ := lt_iSup_iff.mp hlt
    set xs : ℝ := 1 / ((m : ℝ) + 1) with hxs
    have hxs0 : 0 < xs := by positivity
    have hxsl : xs < γ / σbar := by
      by_contra h
      rw [not_lt] at h
      have := hantiOn (Set.mem_Ioi.2 hpos) (Set.mem_Ioi.2 hxs0) h
      exact absurd (lt_trans (lt_of_le_of_lt this hng) hm) (lt_irrefl _)
    have hcI : ContinuousOn (fun x => Cn0 x n0) (Set.Icc xs (γ / σbar)) :=
      hcont.mono fun y hy => Set.mem_Ioi.2 (lt_of_lt_of_le hxs0 hy.1)
    obtain ⟨xstar, hxI, hxeq⟩ := intermediate_value_Icc' hxsl.le hcI ⟨hng.le, hm.le⟩
    have hxstar0 : 0 < xstar := lt_of_lt_of_le hxs0 hxI.1
    have hxstarl : xstar < γ / σbar := by
      rcases lt_or_eq_of_le hxI.2 with h | h
      · exact h
      · exfalso; simp only at hxeq; rw [h] at hxeq; rw [hxeq] at hng; exact lt_irrefl _ hng
    refine ⟨γ - σbar * xstar, ⟨?_, ?_⟩, ?_⟩
    · rw [lt_div_iff₀ hσbar] at hxstarl; linarith
    · have := mul_pos hσbar hxstar0; linarith
    · have : (γ - (γ - σbar * xstar)) / σbar = xstar := by field_simp; ring
      rw [this]; exact hxeq
  · -- the liminf bound, by approximating γ0 from below
    intro γ0 hγ0 heq
    set g : ℕ → ℝ := fun m => γ0 - γ0 / ((m : ℝ) + 2) with hg
    have hg0 : ∀ m, 0 < g m := by
      intro m
      have h2 : (0:ℝ) < (m : ℝ) + 2 := by positivity
      have : γ0 / ((m : ℝ) + 2) < γ0 := by
        rw [div_lt_iff₀ h2]; nlinarith [hγ0.1]
      simp only [hg]; linarith
    have hglt : ∀ m, g m < γ0 := fun m => sub_lt_self _ (by have := hγ0.1; positivity)
    have hgmono : Monotone g := by
      intro m m' hmm
      have : γ0 / ((m' : ℝ) + 2) ≤ γ0 / ((m : ℝ) + 2) :=
        div_le_div_of_nonneg_left hγ0.1.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmm 2)
      simp only [hg]; linarith
    set A : ℝ → Set Ω := fun γ' =>
      {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) n0 (μ 0 - γ')}
      with hA
    have hAmono : Monotone (fun m => A (g m)) := by
      intro m m' hmm ω hω
      exact ⟨hω.1, lt_of_le_of_lt (by linarith [hgmono hmm]) hω.2⟩
    have hsub : A γ0 ⊆ ⋃ m, A (g m) := by
      intro ω hω
      obtain ⟨hb, hlt⟩ := hω
      set d := (⨅ n, GreedyRS.Greedy.runMean (fun i j => X i j ω) 0 (n0 + n)) - (μ 0 - γ0) with hd
      have hdpos : 0 < d := by simp only [hd]; linarith
      obtain ⟨m, hm⟩ := exists_nat_gt (γ0 / d)
      have h2 : (0:ℝ) < (m : ℝ) + 2 := by positivity
      have : γ0 / ((m : ℝ) + 2) < d := by
        rw [div_lt_iff₀ h2]; rw [div_lt_iff₀ hdpos] at hm; nlinarith
      refine Set.mem_iUnion.2 ⟨m, hb, ?_⟩
      simp only [hg]; linarith
    calc P (A γ0) ≤ P (⋃ m, A (g m)) := measure_mono hsub
      _ = ⨆ m, P (A (g m)) := hAmono.measure_iUnion
      _ ≤ _ := by
        refine iSup_le fun m => ?_
        refine GreedyRS.EFG.theorem3_liminf_at_level P μ v X hX hv γ σbar hγ hσbar hgap hvar n0 hn0 ng
          (g m) ⟨hg0 m, (hglt m).trans hγ0.2⟩ ?_
        rw [← heq]
        apply hstrict
        · exact Set.mem_Ioi.2 (div_pos (by linarith [hγ0.2]) hσbar)
        · exact Set.mem_Ioi.2 (div_pos (by linarith [hglt m, hγ0.2]) hσbar)
        · exact div_lt_div_of_pos_right (by linarith [hglt m]) hσbar
