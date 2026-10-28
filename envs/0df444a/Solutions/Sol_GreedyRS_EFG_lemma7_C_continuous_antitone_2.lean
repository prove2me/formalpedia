-- Prove2me | solution 2 for GreedyRS.EFG.lemma7_C_continuous_antitone
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T10:59:12.077736+00:00
-- url     : https://prove2.me/submissions/e39d5004-4213-4d7a-af70-ede2f91fa4c5

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting

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

namespace GRSFin
open GreedyRS.Greedy GRSHelp

lemma tail_bound (n : ℕ) {x : ℝ} (hx : 0 < x) :
    stdNormalSeq {z | x ≤ zbar z n} ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * x ^ 2 / 2)) := by
  rcases Nat.eq_zero_or_pos n with h | hn
  · subst h
    calc _ ≤ 1 := prob_le_one
      _ = _ := by simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hset : {z : ℕ → ℝ | x ≤ zbar z n} =
      (fun z : ℕ → ℝ => ∑ j ∈ Finset.range n, z j) ⁻¹' Set.Ici ((n : ℝ) * x) := by
    ext z
    simp only [zbar, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici]
    rw [le_div_iff₀ hn', mul_comm]
  rw [hset, ← Measure.map_apply (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))
    measurableSet_Ici, map_partialSum]
  have hint : Integrable (fun y => Real.exp (x * id y)) (gaussianReal 0 (n : ℝ≥0)) := by
    simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := (n : ℝ≥0)) x
  have hch := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 (n : ℝ≥0)) (X := id) ((n : ℝ) * x) hx.le hint
  rw [mgf_gaussianReal (μ := 0) (v := (n : ℝ≥0)) (p := gaussianReal 0 (n : ℝ≥0)) (X := id)
    Measure.map_id x] at hch
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  apply ENNReal.ofReal_le_ofReal
  refine le_trans (le_of_eq_of_le (by rfl) hch) (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

lemma C_fin {x : ℝ} (hx : 0 < x) (n0 : ℕ) : Cn0 x n0 < ⊤ := by
  set r : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-x ^ 2 / 2)) with hr
  have hr1 : r < 1 := by
    rw [hr, ENNReal.ofReal_lt_one, ← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    have := pow_pos hx 2
    linarith
  set A : ℕ → Set (ℕ → ℝ) := fun n => {z | x ≤ zbar z (n0 + n)} with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_le measurable_const (measurable_zbar _)
  have hpt : ∀ z, ((crossTime x n0 z : ℕ∞) : ℝ≥0∞) ≤
      (n0 : ℝ≥0∞) + ∑' n, (A n).indicator (1 : (ℕ → ℝ) → ℝ≥0∞) z := by
    intro z
    rcases eq_or_ne (crossTime x n0 z) ⊤ with h | h
    · have hall : ∀ n, z ∈ A n := by
        intro n
        by_contra hc
        simp only [hA, Set.mem_setOf_eq, not_le] at hc
        have := crossTime_le (x := x) (n0 := n0) (z := z) (n := n0 + n) (by omega) hc
        rw [h] at this
        exact absurd this (not_le.mpr (ENat.coe_lt_top _))
      have : ∑' n, (A n).indicator (1 : (ℕ → ℝ) → ℝ≥0∞) z = ⊤ := by
        simp only [Set.indicator_of_mem (hall _), Pi.one_apply]
        exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
      rw [this]
      simp
    · obtain ⟨m, hm, h1, h2⟩ := crossTime_spec (lt_top_iff_ne_top.mpr h)
      rw [hm]
      have hmem : ∀ n, n < m - n0 → z ∈ A n := by
        intro n hn
        by_contra hc
        simp only [hA, Set.mem_setOf_eq, not_le] at hc
        have := crossTime_le (x := x) (n0 := n0) (z := z) (n := n0 + n) (by omega) hc
        rw [hm] at this
        have : m ≤ n0 + n := by exact_mod_cast this
        omega
      have hsum : ∑ n ∈ Finset.range (m - n0), (A n).indicator (1 : (ℕ → ℝ) → ℝ≥0∞) z =
          ((m - n0 : ℕ) : ℝ≥0∞) := by
        rw [Finset.sum_congr rfl (fun n hn => by
          rw [Set.indicator_of_mem (hmem n (Finset.mem_range.mp hn))])]
        simp
      have hle := ENNReal.sum_le_tsum (f := fun n => (A n).indicator (1 : (ℕ → ℝ) → ℝ≥0∞) z)
        (Finset.range (m - n0))
      rw [hsum] at hle
      calc ((m : ℕ∞) : ℝ≥0∞) = (n0 : ℝ≥0∞) + ((m - n0 : ℕ) : ℝ≥0∞) := by
            rw [ENat.toENNReal_coe, ← Nat.cast_add, Nat.add_sub_cancel' h1]
        _ ≤ _ := by gcongr
  unfold Cn0
  calc ∫⁻ z, ((crossTime x n0 z : ℕ∞) : ℝ≥0∞) ∂stdNormalSeq
      ≤ ∫⁻ z, ((n0 : ℝ≥0∞) + ∑' n, (A n).indicator (1 : (ℕ → ℝ) → ℝ≥0∞) z) ∂stdNormalSeq :=
        lintegral_mono hpt
    _ = (n0 : ℝ≥0∞) + ∑' n, stdNormalSeq (A n) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_tsum (fun n => (measurable_one.indicator (hAm n)).aemeasurable)]
        congr 1
        refine tsum_congr fun n => ?_
        exact lintegral_indicator_one (hAm n)
    _ ≤ (n0 : ℝ≥0∞) + ∑' n : ℕ, r ^ n := by
        gcongr with n
        refine (tail_bound (n0 + n) hx).trans ?_
        rw [hr, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        push_cast
        have := sq_nonneg x
        have h0 : (0:ℝ) ≤ n0 := Nat.cast_nonneg _
        nlinarith [mul_nonneg h0 this]
    _ < ⊤ := by
        rw [ENNReal.tsum_geometric]
        exact ENNReal.add_lt_top.2 ⟨ENNReal.natCast_lt_top n0,
          ENNReal.inv_lt_top.2 (tsub_pos_of_lt hr1)⟩

end GRSFin

open GreedyRS.Greedy GRSHelp GRSFin in
theorem solution (n0 : ℕ) (hn0 : 1 ≤ n0) :
    StrictAntiOn (fun x => GreedyRS.Greedy.Cn0 x n0) (Set.Ioi 0) ∧
    ContinuousOn (fun x => GreedyRS.Greedy.Cn0 x n0) (Set.Ioi 0) := by
  have hfin : ∀ x : ℝ, 0 < x → Cn0 x n0 < ⊤ := fun x hx => C_fin hx n0
  have hanti : Antitone (fun x => Cn0 x n0) := by
    intro x y hxy
    exact lintegral_mono fun z => ENat.toENNReal_le.mpr (crossTime_anti hxy n0 z)
  refine ⟨?_, ?_⟩
  · -- strict monotonicity
    intro x1 hx1 x2 hx2 hlt
    show Cn0 x2 n0 < Cn0 x1 n0
    unfold Cn0
    refine lintegral_strict_mono_of_ae_le_of_ae_lt_on (measurable_crossTime_enn x1 n0).aemeasurable
      (hfin x2 hx2).ne (ae_of_all _ fun z => ENat.toENNReal_le.mpr (crossTime_anti hlt.le n0 z))
      (s := {z | x1 ≤ zbar z n0 ∧ zbar z n0 < x2}) (zbar_Ico_pos n0 hn0 hlt).ne' ?_
    refine ae_of_all _ fun z hz => ?_
    have h1 : crossTime x2 n0 z ≤ n0 := crossTime_le le_rfl hz.2
    have h2 : ((n0 + 1 : ℕ) : ℕ∞) ≤ crossTime x1 n0 z := by
      apply le_crossTime
      intro n hn hzn
      have : n ≠ n0 := by
        rintro rfl; exact absurd hz.1 (not_le.mpr hzn)
      exact_mod_cast (show n0 + 1 ≤ n by omega)
    apply ENat.toENNReal_lt.mpr
    refine lt_of_le_of_lt h1 (lt_of_lt_of_le ?_ h2)
    exact_mod_cast Nat.lt_succ_self n0
  · -- continuity
    intro x0 hx0
    have hx0 : (0 : ℝ) < x0 := hx0
    apply ContinuousAt.continuousWithinAt
    -- right limit via monotone convergence
    have hR : ⨆ m : ℕ, Cn0 (x0 + 1 / ((m : ℝ) + 1)) n0 = Cn0 x0 n0 := by
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
    -- left limit via dominated (monotone decreasing) convergence
    have hL : ⨅ m : ℕ, Cn0 (x0 - x0 / ((m : ℝ) + 2)) n0 = Cn0 x0 n0 := by
      unfold Cn0
      have hanti' : Antitone (fun (m : ℕ) (z : ℕ → ℝ) =>
          ((crossTime (x0 - x0 / ((m : ℝ) + 2)) n0 z : ℕ∞) : ℝ≥0∞)) := by
        intro m m' hmm z
        apply ENat.toENNReal_le.mpr
        apply crossTime_anti
        have : x0 / ((m' : ℝ) + 2) ≤ x0 / ((m : ℝ) + 2) :=
          div_le_div_of_nonneg_left hx0.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmm 2)
        linarith
      have h0 : (0 : ℝ) < x0 - x0 / (((0 : ℕ) : ℝ) + 2) := by
        norm_num; linarith
      rw [← lintegral_iInf (fun m => measurable_crossTime_enn _ n0) hanti' (hfin _ h0).ne]
      apply lintegral_congr
      intro z
      rw [← ENat.toENNReal_iInf]
      congr 1
      apply le_antisymm
      · rcases eq_or_ne (crossTime x0 n0 z) ⊤ with h | h
        · rw [h]; exact le_top
        obtain ⟨n, hn, h1, h2⟩ := crossTime_spec (lt_top_iff_ne_top.mpr h)
        obtain ⟨m, hm⟩ := exists_nat_gt (x0 / (x0 - zbar z n))
        have hpos : 0 < x0 - zbar z n := sub_pos.mpr h2
        have : x0 / ((m : ℝ) + 2) < x0 - zbar z n := by
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hpos] at hm
          nlinarith
        rw [hn]
        exact iInf_le_of_le m (crossTime_le h1 (by linarith))
      · exact le_iInf fun m => crossTime_anti (sub_le_self _ (by positivity)) n0 z
    rw [ContinuousAt, tendsto_order]
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · rw [← hR] at ha
      obtain ⟨m, hm⟩ := lt_iSup_iff.mp ha
      have hy : x0 < x0 + 1 / ((m : ℝ) + 1) := lt_add_of_pos_right _ (by positivity)
      filter_upwards [Iio_mem_nhds hy] with y hy'
      exact lt_of_lt_of_le hm (hanti (le_of_lt hy'))
    · rw [← hL] at hb
      obtain ⟨m, hm⟩ := iInf_lt_iff.mp hb
      have hy : x0 - x0 / ((m : ℝ) + 2) < x0 := sub_lt_self _ (by positivity)
      filter_upwards [Ioi_mem_nhds hy] with y hy'
      exact lt_of_le_of_lt (hanti (le_of_lt hy')) hm
