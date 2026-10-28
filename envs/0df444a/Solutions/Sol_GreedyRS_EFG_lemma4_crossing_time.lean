-- Prove2me | solution 1 for GreedyRS.EFG.lemma4_crossing_time
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T10:48:04.438382+00:00
-- url     : https://prove2.me/submissions/adbf6ef7-b398-4bfa-8cc8-f01ae482e4c8

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting
import Theorems.Thm_GreedyRS_EFG_eq5_1_crossing_sandwich
import Theorems.Thm_GreedyRS_Greedy_lemma2_crossing_time

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

namespace GRSHelp
open GreedyRS.Greedy

lemma measurable_blockCross (x : ℝ) (n0 : ℕ) : Measurable (GreedyRS.EFG.blockCross x n0) := by
  have henn : Measurable (fun z => ((GreedyRS.EFG.blockCross x n0 z : ℕ∞) : ℝ≥0∞)) := by
    have : (fun z => ((GreedyRS.EFG.blockCross x n0 z : ℕ∞) : ℝ≥0∞)) =
        fun z => ⨅ m : ℕ, (if 1 ≤ m ∧ zbar z (m * n0) < x then (m : ℝ≥0∞) else ⊤) := by
      funext z
      unfold GreedyRS.EFG.blockCross
      rw [ENat.toENNReal_iInf]
      congr 1; funext m
      rw [ENat.toENNReal_iInf]
      by_cases h : 1 ≤ m ∧ zbar z (m * n0) < x
      · simp [h]
      · simp [h]
    rw [this]
    apply Measurable.iInf
    intro m
    apply Measurable.ite _ measurable_const measurable_const
    by_cases hm : 1 ≤ m
    · simp only [hm, true_and]
      exact measurableSet_lt (measurable_zbar _) measurable_const
    · simp [hm]
  apply measurable_to_countable'
  intro k
  have : GreedyRS.EFG.blockCross x n0 ⁻¹' {k} =
      (fun z => ((GreedyRS.EFG.blockCross x n0 z : ℕ∞) : ℝ≥0∞)) ⁻¹' {(k : ℝ≥0∞)} := by
    ext z; simp
  rw [this]
  exact henn (measurableSet_singleton _)

lemma prob_eq_one_of_ae {p : (ℕ → ℝ) → Prop} (h : ∀ᵐ z ∂stdNormalSeq, p z) :
    stdNormalSeq {z | p z} = 1 := by
  apply le_antisymm prob_le_one
  rw [← measure_univ (μ := stdNormalSeq)]
  apply measure_mono_ae
  filter_upwards [h] with z hz _
  exact hz

end GRSHelp

open GreedyRS.Greedy GRSHelp in
theorem solution (n0 : ℕ) (hn0 : 1 ≤ n0) :
    (∀ x : ℝ, 0 < x →
      GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.crossTime x n0 z < ⊤} = 1 ∧ GreedyRS.Greedy.Cn0 x n0 < ⊤) ∧
    (∀ x : ℝ, x < 0 →
      0 < GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.crossTime x n0 z < ⊤} ∧
      GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.crossTime x n0 z < ⊤} < 1 ∧ GreedyRS.Greedy.Cn0 x n0 = ⊤) ∧
    (GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.crossTime 0 n0 z < ⊤} = 1 ∧ GreedyRS.Greedy.Cn0 0 n0 = ⊤) := by
  obtain ⟨L1, -, -, L4, -, -, L0p, L0C⟩ := GreedyRS.Greedy.lemma2_crossing_time
  have hn0' : (n0 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n0
  -- the lower comparison C(x;1) ≤ C(x;n0)
  have hlow : ∀ x : ℝ, Cn0 x 1 ≤ Cn0 x n0 := fun x =>
    lintegral_mono fun z => ENat.toENNReal_le.mpr
      ((GreedyRS.EFG.eq5_1_crossing_sandwich n0 hn0 x).1 z)
  refine ⟨fun x hx => ?_, fun x hx => ?_, ?_⟩
  · -- x > 0
    obtain ⟨_, h2, h3⟩ := GreedyRS.EFG.eq5_1_crossing_sandwich n0 hn0 x
    have hmap : stdNormalSeq.map (GreedyRS.EFG.blockCross x n0) =
        stdNormalSeq.map (crossTime (Real.sqrt n0 * x) 1) := by
      ext s hs
      rw [Measure.map_apply (measurable_blockCross x n0) hs,
        Measure.map_apply (measurable_crossTime _ 1) hs, h3 s]
    have hint : ∫⁻ z, ((GreedyRS.EFG.blockCross x n0 z : ℕ∞) : ℝ≥0∞) ∂stdNormalSeq =
        Cn0 (Real.sqrt n0 * x) 1 := by
      unfold Cn0
      rw [← lintegral_map (f := fun t : ℕ∞ => (t : ℝ≥0∞)) Measurable.of_discrete
          (measurable_blockCross x n0), hmap,
        lintegral_map Measurable.of_discrete (measurable_crossTime _ 1)]
    have hpos : 0 < Real.sqrt n0 * x := mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hn0)) hx
    have hCfin : Cn0 x n0 < ⊤ := by
      calc Cn0 x n0 ≤ ∫⁻ z, (n0 : ℝ≥0∞) * ((GreedyRS.EFG.blockCross x n0 z : ℕ∞) : ℝ≥0∞) ∂stdNormalSeq := by
            unfold Cn0
            refine lintegral_mono fun z => ?_
            have := ENat.toENNReal_le.mpr (h2 z)
            simpa using this
        _ = (n0 : ℝ≥0∞) * Cn0 (Real.sqrt n0 * x) 1 := by
            have hm : Measurable (fun z => ((GreedyRS.EFG.blockCross x n0 z : ℕ∞) : ℝ≥0∞)) :=
              Measurable.of_discrete.comp (measurable_blockCross x n0)
            rw [lintegral_const_mul _ hm, hint]
        _ < ⊤ := by
            rw [(L1 _ hpos).2]
            exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top n0) ENNReal.ofReal_lt_top
    refine ⟨?_, hCfin⟩
    apply prob_eq_one_of_ae
    filter_upwards [ae_lt_top (measurable_crossTime_enn x n0) hCfin.ne] with z hz
    exact ENat.toENNReal_lt_top.mp hz
  · -- x < 0
    obtain ⟨hC1, hP1⟩ := L4 x hx
    refine ⟨?_, ?_, ?_⟩
    · have hsub : {z : ℕ → ℝ | x - 1 ≤ zbar z n0 ∧ zbar z n0 < x} ⊆ {z | crossTime x n0 z < ⊤} := by
        intro z hz
        exact lt_of_le_of_lt (crossTime_le le_rfl hz.2) (ENat.coe_lt_top n0)
      exact lt_of_lt_of_le (zbar_Ico_pos n0 hn0 (by linarith)) (measure_mono hsub)
    · have hsub : {z : ℕ → ℝ | crossTime x n0 z < ⊤} ⊆ {z | crossTime x 1 z < ⊤} := fun z hz =>
        lt_of_le_of_lt ((GreedyRS.EFG.eq5_1_crossing_sandwich n0 hn0 x).1 z) hz
      refine lt_of_le_of_lt (measure_mono hsub) ?_
      rw [hP1, ENNReal.ofReal_lt_one]
      have := Real.exp_pos (-∑' n : ℕ, Phi (Real.sqrt ((n : ℝ) + 1) * x) / ((n : ℝ) + 1))
      linarith
    · exact top_le_iff.mp (hC1 ▸ hlow x)
  · -- x = 0
    refine ⟨?_, top_le_iff.mp (L0C ▸ hlow 0)⟩
    obtain ⟨_, h2, h3⟩ := GreedyRS.EFG.eq5_1_crossing_sandwich n0 hn0 0
    have hB : stdNormalSeq {z | GreedyRS.EFG.blockCross 0 n0 z < ⊤} = 1 := by
      have := h3 (Set.Iio ⊤)
      simp only [mul_zero] at this
      exact this.trans L0p
    apply le_antisymm prob_le_one
    rw [← hB]
    apply measure_mono
    intro z hz
    have hz' : GreedyRS.EFG.blockCross 0 n0 z < ⊤ := hz
    refine lt_of_le_of_lt (h2 z) ?_
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hz'.ne
    rw [← hk]
    exact_mod_cast ENat.coe_lt_top (n0 * k)
