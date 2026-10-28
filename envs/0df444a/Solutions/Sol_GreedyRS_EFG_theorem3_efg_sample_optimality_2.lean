-- Prove2me | solution 2 for GreedyRS.EFG.theorem3_efg_sample_optimality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T11:01:04.85565+00:00
-- url     : https://prove2.me/submissions/778decde-aa8b-42c7-82cc-f63ae26b25b0

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting
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

namespace GRSWald
open GreedyRS.Greedy GRSHelp

/-- `{τ > j}` for `τ = Ñ(0; 1)`. -/
def Ev (j : ℕ) : Set (ℕ → ℝ) := {z | (j : ℕ∞) < crossTime 0 1 z}

lemma measurableSet_Ev (j : ℕ) : MeasurableSet (Ev j) :=
  measurable_crossTime 0 1 (MeasurableSet.of_discrete (s := Set.Ioi (j : ℕ∞)))

lemma Ev_iff (j : ℕ) (z : ℕ → ℝ) :
    z ∈ Ev j ↔ ∀ n, 1 ≤ n → n ≤ j → 0 ≤ ∑ i ∈ Finset.range n, z i := by
  constructor
  · intro h n h1 h2
    by_contra hc
    rw [not_le] at hc
    have hz : zbar z n < 0 := div_neg_of_neg_of_pos hc (by exact_mod_cast h1)
    have := crossTime_le (x := 0) (n0 := 1) (z := z) h1 hz
    have h3 : (j : ℕ∞) < n := lt_of_lt_of_le h this
    have : j < n := by exact_mod_cast h3
    omega
  · intro h
    show (j : ℕ∞) < crossTime 0 1 z
    have : ((j + 1 : ℕ) : ℕ∞) ≤ crossTime 0 1 z := by
      apply le_crossTime
      intro n h1 h2
      by_contra hc
      have hc' : n < j + 1 := by
        rw [not_le] at hc; exact_mod_cast hc
      have := h n h1 (by omega)
      have : 0 ≤ zbar z n := div_nonneg this (Nat.cast_nonneg _)
      linarith
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self j) this

lemma sum_restrict (j n : ℕ) (hn : n ≤ j) (z : ℕ → ℝ) :
    ∑ i : Finset.range j, (if (i : ℕ) < n then (1 : ℝ) else 0) * z i = ∑ i ∈ Finset.range n, z i := by
  rw [Finset.sum_coe_sort (Finset.range j) (fun i => (if i < n then (1 : ℝ) else 0) * z i)]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma indep_Ev (j : ℕ) :
    IndepFun (fun z : ℕ → ℝ => z j) ((Ev j).indicator (fun _ => (1 : ℝ))) stdNormalSeq := by
  have h := iIndep_coord.indepFun_finset (Finset.range j) {j} (by simp)
    (fun i => measurable_pi_apply i)
  set F : Set (Finset.range j → ℝ) := {u | ∀ n, 1 ≤ n → n ≤ j →
    0 ≤ ∑ i : Finset.range j, (if (i : ℕ) < n then (1 : ℝ) else 0) * u i} with hFdef
  have hF : MeasurableSet F := by
    have : F = ⋂ n ∈ Finset.Icc 1 j,
        {u : Finset.range j → ℝ | 0 ≤ ∑ i : Finset.range j, (if (i : ℕ) < n then (1 : ℝ) else 0) * u i} := by
      ext u
      simp only [hFdef, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_Icc]
      constructor
      · intro h n hn; exact h n hn.1 hn.2
      · intro h n h1 h2; exact h n ⟨h1, h2⟩
    rw [this]
    exact Finset.measurableSet_biInter _ (fun n _ => measurableSet_le measurable_const
      (Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_pi_apply i))))
  have hEv : ∀ z : ℕ → ℝ, z ∈ Ev j ↔ (fun (i : Finset.range j) => z i) ∈ F := by
    intro z
    rw [Ev_iff]
    simp only [hFdef, Set.mem_setOf_eq]
    constructor
    · intro h n h1 h2; rw [sum_restrict j n h2]; exact h n h1 h2
    · intro h n h1 h2; rw [← sum_restrict j n h2]; exact h n h1 h2
  have h2 : IndepFun (F.indicator (fun _ => (1 : ℝ)) ∘ (fun z (i : Finset.range j) => z i))
      ((fun u : ({j} : Finset ℕ) → ℝ => u ⟨j, Finset.mem_singleton_self j⟩) ∘
        (fun z (i : ({j} : Finset ℕ)) => z i)) stdNormalSeq :=
    h.comp (measurable_const.indicator hF)
      (measurable_pi_apply (X := fun _ : ({j} : Finset ℕ) => ℝ) ⟨j, Finset.mem_singleton_self j⟩)
  have e2 : (Ev j).indicator (fun _ => (1 : ℝ)) =
      F.indicator (fun _ => (1 : ℝ)) ∘ (fun z (i : Finset.range j) => z i) := by
    funext z
    simp only [Function.comp, Set.indicator_apply]
    by_cases hz : z ∈ Ev j
    · rw [Set.indicator_of_mem hz, if_pos ((hEv z).mp hz)]
    · rw [Set.indicator_of_notMem hz, if_neg (fun h => hz ((hEv z).mpr h))]
  rw [e2]
  exact h2.symm

lemma tsum_ind (t : ℕ∞) :
    ∑' j : ℕ, (if (j : ℕ∞) < t then (1 : ℝ≥0∞) else 0) = (t : ℝ≥0∞) := by
  induction t using ENat.recTopCoe with
  | top =>
    simp only [ENat.coe_lt_top, if_true, ENat.toENNReal_top]
    exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  | coe m =>
    rw [tsum_eq_sum (s := Finset.range m)]
    · rw [Finset.sum_congr rfl (fun j hj => by
        rw [if_pos (by exact_mod_cast Finset.mem_range.mp hj)])]
      simp
    · intro j hj
      rw [if_neg]
      rw [Finset.mem_range, not_lt] at hj
      exact_mod_cast not_lt.mpr hj

lemma C_zero_top : Cn0 0 1 = ⊤ := by
  by_contra hne
  have hCfin : ∫⁻ z, ((crossTime 0 1 z : ℕ∞) : ℝ≥0∞) ∂stdNormalSeq ≠ ⊤ := hne
  have hfin_ae : ∀ᵐ z ∂stdNormalSeq, crossTime 0 1 z < ⊤ :=
    (ae_lt_top (measurable_crossTime_enn 0 1) hCfin).mono fun z hz => ENat.toENNReal_lt_top.mp hz
  -- moments of a coordinate
  have hmapj : ∀ j, stdNormalSeq.map (fun z : ℕ → ℝ => z j) = gaussianReal 0 1 := map_coord
  have hintj : ∀ j, Integrable (fun z : ℕ → ℝ => z j) stdNormalSeq := by
    intro j
    have : Integrable id (gaussianReal 0 1) := (memLp_id_gaussianReal 1).integrable le_rfl
    rw [← hmapj j] at this
    exact (integrable_map_measure aestronglyMeasurable_id
      (measurable_pi_apply j).aemeasurable).mp this
  have hmean : ∀ j, ∫ z, z j ∂stdNormalSeq = 0 := by
    intro j
    have := integral_map (μ := stdNormalSeq) (measurable_pi_apply j).aemeasurable
      (aestronglyMeasurable_id (α := ℝ))
    rw [hmapj j] at this
    calc ∫ z, z j ∂stdNormalSeq = ∫ y, id y ∂(gaussianReal 0 1) := this.symm
      _ = 0 := integral_id_gaussianReal
  set K : ℝ≥0∞ := ∫⁻ z, ‖z 0‖ₑ ∂stdNormalSeq with hK
  have hKfin : K ≠ ⊤ := (hintj 0).2.ne
  have hKe : ∀ j, ∫⁻ z, ‖z j‖ₑ ∂stdNormalSeq = ∫⁻ x, ‖x‖ₑ ∂(gaussianReal 0 1) := fun j => by
    rw [← hmapj j, lintegral_map measurable_enorm (measurable_pi_apply j)]
  have hKj : ∀ j, ∫⁻ z, ‖z j‖ₑ ∂stdNormalSeq = K := fun j => (hKe j).trans (hKe 0).symm
  -- the dominating function
  set Tb : (ℕ → ℝ) → ℝ≥0∞ := fun z => ∑' j, ‖z j‖ₑ * (Ev j).indicator 1 z with hTb
  have hTbm : Measurable Tb := Measurable.ennreal_tsum fun j =>
    (measurable_enorm.comp (measurable_pi_apply j)).mul (measurable_one.indicator (measurableSet_Ev j))
  have hmj : ∀ j, Measurable (fun z : ℕ → ℝ => ‖z j‖ₑ * (Ev j).indicator (1 : (ℕ → ℝ) → ℝ≥0∞) z) :=
    fun j => (measurable_enorm.comp (measurable_pi_apply j)).mul
      (measurable_one.indicator (measurableSet_Ev j))
  have hTbfin : ∫⁻ z, Tb z ∂stdNormalSeq ≠ ⊤ := by
    simp only [hTb]
    rw [lintegral_tsum (fun j => (hmj j).aemeasurable)]
    have hterm : ∀ j, ∫⁻ z, ‖z j‖ₑ * (Ev j).indicator 1 z ∂stdNormalSeq = K * stdNormalSeq (Ev j) := by
      intro j
      have hind : IndepFun (fun z : ℕ → ℝ => ‖z j‖ₑ) ((Ev j).indicator (1 : (ℕ → ℝ) → ℝ≥0∞))
          stdNormalSeq := by
        have := (indep_Ev j).comp (φ := fun x : ℝ => ‖x‖ₑ) (ψ := fun r : ℝ => ENNReal.ofReal r)
          measurable_enorm ENNReal.measurable_ofReal
        have e : (Ev j).indicator (1 : (ℕ → ℝ) → ℝ≥0∞) =
            (fun r : ℝ => ENNReal.ofReal r) ∘ (Ev j).indicator (fun _ => (1 : ℝ)) := by
          funext w
          by_cases hw : w ∈ Ev j <;> simp [hw]
        rw [e]
        exact this
      have := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
        (measurable_enorm.comp (measurable_pi_apply j))
        (measurable_one.indicator (measurableSet_Ev j)) hind
      simp only [Pi.mul_apply, Function.comp_apply] at this
      rw [this, hKj j, lintegral_indicator_one (measurableSet_Ev j)]
    simp_rw [hterm]
    rw [ENNReal.tsum_mul_left]
    have hsum : ∑' j, stdNormalSeq (Ev j) = ∫⁻ z, ((crossTime 0 1 z : ℕ∞) : ℝ≥0∞) ∂stdNormalSeq := by
      calc ∑' j, stdNormalSeq (Ev j) = ∑' j, ∫⁻ z, (Ev j).indicator (1 : (ℕ → ℝ) → ℝ≥0∞) z ∂stdNormalSeq := by
            congr 1; funext j; rw [lintegral_indicator_one (measurableSet_Ev j)]
        _ = ∫⁻ z, ∑' j, (Ev j).indicator (1 : (ℕ → ℝ) → ℝ≥0∞) z ∂stdNormalSeq :=
            (lintegral_tsum (fun j => (measurable_one.indicator (measurableSet_Ev j)).aemeasurable)).symm
        _ = ∫⁻ z, ((crossTime 0 1 z : ℕ∞) : ℝ≥0∞) ∂stdNormalSeq := by
            refine lintegral_congr fun z => ?_
            rw [← tsum_ind (crossTime 0 1 z)]
            congr 1; funext j
            simp only [Set.indicator_apply, Ev, Set.mem_setOf_eq, Pi.one_apply]
    rw [hsum]
    exact ENNReal.mul_ne_top hKfin hCfin
  -- partial sums and Wald's identity
  set g : ℕ → (ℕ → ℝ) → ℝ := fun N z => ∑ j ∈ Finset.range N, (Ev j).indicator (fun z => z j) z
    with hg
  set G : (ℕ → ℝ) → ℝ := fun z => ∑' j, (Ev j).indicator (fun z => z j) z with hGdef
  have hgm : ∀ N, Measurable (g N) := fun N =>
    Finset.measurable_sum _ (fun j _ => (measurable_pi_apply j).indicator (measurableSet_Ev j))
  have hgint : ∀ N, ∫ z, g N z ∂stdNormalSeq = 0 := by
    intro N
    simp only [hg]
    rw [integral_finset_sum _ (fun j _ => (hintj j).indicator (measurableSet_Ev j))]
    apply Finset.sum_eq_zero
    intro j _
    have e : (Ev j).indicator (fun z : ℕ → ℝ => z j) =
        (fun z : ℕ → ℝ => z j) * (Ev j).indicator (fun _ => (1 : ℝ)) := by
      funext z; by_cases hz : z ∈ Ev j <;> simp [hz]
    rw [e, (indep_Ev j).integral_mul_eq_mul_integral (measurable_pi_apply j).aestronglyMeasurable
      ((measurable_const.indicator (measurableSet_Ev j)).aestronglyMeasurable), hmean j, zero_mul]
  have hgood : ∀ z, crossTime 0 1 z < ⊤ →
      ∃ m : ℕ, (∀ N, m ≤ N → g N z = G z) ∧ G z < 0 := by
    intro z hz
    obtain ⟨m, hm, h1, h2⟩ := crossTime_spec hz
    have hmem : ∀ j, z ∈ Ev j ↔ j < m := by
      intro j
      simp only [Ev, Set.mem_setOf_eq, hm]
      exact Nat.cast_lt
    have hG : G z = ∑ j ∈ Finset.range m, z j := by
      simp only [hGdef]
      rw [tsum_eq_sum (s := Finset.range m)]
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [Set.indicator_of_mem ((hmem j).2 (Finset.mem_range.1 hj))]
      · intro j hj
        rw [Set.indicator_of_notMem (fun h => hj (Finset.mem_range.2 ((hmem j).1 h)))]
    refine ⟨m, fun N hN => ?_, ?_⟩
    · rw [hG]
      simp only [hg]
      rw [← Finset.sum_range_add_sum_Ico _ hN]
      rw [Finset.sum_eq_zero (s := Finset.Ico m N) (fun j hj => Set.indicator_of_notMem (fun h => by
        have := (hmem j).1 h
        rw [Finset.mem_Ico] at hj
        omega) _), add_zero]
      exact Finset.sum_congr rfl fun j hj => Set.indicator_of_mem ((hmem j).2 (Finset.mem_range.1 hj)) _
    · rw [hG]
      have hm0 : (0 : ℝ) < m := by exact_mod_cast h1
      have h3 : zbar z m < 0 := h2
      unfold zbar at h3
      by_contra hc
      rw [not_lt] at hc
      have := div_nonneg hc hm0.le
      linarith
  have hTae : ∀ᵐ z ∂stdNormalSeq, Tb z < ⊤ := ae_lt_top hTbm hTbfin
  have hbound : ∀ N, ∀ᵐ z ∂stdNormalSeq, ‖g N z‖ ≤ (Tb z).toReal := by
    intro N
    filter_upwards [hTae] with z hz
    have hterm_ne : ∀ j, ‖z j‖ₑ * (Ev j).indicator (1 : (ℕ → ℝ) → ℝ≥0∞) z ≠ ⊤ := by
      intro j; by_cases hzj : z ∈ Ev j <;> simp [hzj]
    calc ‖g N z‖ ≤ ∑ j ∈ Finset.range N, ‖(Ev j).indicator (fun z => z j) z‖ := norm_sum_le _ _
      _ = ∑ j ∈ Finset.range N, (‖z j‖ₑ * (Ev j).indicator (1 : (ℕ → ℝ) → ℝ≥0∞) z).toReal := by
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hzj : z ∈ Ev j <;> simp [hzj]
      _ = (∑ j ∈ Finset.range N, ‖z j‖ₑ * (Ev j).indicator (1 : (ℕ → ℝ) → ℝ≥0∞) z).toReal :=
          (ENNReal.toReal_sum (fun j _ => hterm_ne j)).symm
      _ ≤ (Tb z).toReal := ENNReal.toReal_mono hz.ne (ENNReal.sum_le_tsum _)
  have hlim : ∀ᵐ z ∂stdNormalSeq, Tendsto (fun N => g N z) atTop (nhds (G z)) := by
    filter_upwards [hfin_ae] with z hz
    obtain ⟨m, hgm', -⟩ := hgood z hz
    exact tendsto_atTop_of_eventually_const (i₀ := m) hgm'
  have hbint : Integrable (fun z => (Tb z).toReal) stdNormalSeq :=
    integrable_toReal_of_lintegral_ne_top hTbm.aemeasurable hTbfin
  have hDCT := tendsto_integral_of_dominated_convergence _ (fun N => (hgm N).aestronglyMeasurable)
    hbint hbound hlim
  simp only [hgint] at hDCT
  have hG0 : ∫ z, G z ∂stdNormalSeq = 0 := tendsto_nhds_unique hDCT tendsto_const_nhds
  have hGm : AEStronglyMeasurable G stdNormalSeq :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun N => (hgm N).aestronglyMeasurable) hlim
  have hGb : ∀ᵐ z ∂stdNormalSeq, ‖G z‖ ≤ (Tb z).toReal := by
    filter_upwards [ae_all_iff.2 hbound, hfin_ae] with z hb hz
    obtain ⟨m, hgm', -⟩ := hgood z hz
    rw [← hgm' m le_rfl]
    exact hb m
  have hGint : Integrable G stdNormalSeq := hbint.mono' hGm hGb
  have hneg : ∀ᵐ z ∂stdNormalSeq, 0 < -G z := by
    filter_upwards [hfin_ae] with z hz
    obtain ⟨m, -, hlt⟩ := hgood z hz
    linarith
  have hpos : 0 < ∫ z, -G z ∂stdNormalSeq := by
    rw [integral_pos_iff_support_of_nonneg_ae (hneg.mono fun z hz => hz.le) hGint.neg]
    by_contra h0
    rw [not_lt, nonpos_iff_eq_zero] at h0
    have h1 : ∀ᵐ z ∂stdNormalSeq, -G z = 0 :=
      (measure_eq_zero_iff_ae_notMem.1 h0).mono fun z hz => Function.notMem_support.1 hz
    obtain ⟨z, hz1, hz2⟩ := (hneg.and h1).exists
    linarith
  rw [integral_neg, hG0] at hpos
  simp at hpos

end GRSWald

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
    have hC0 : Cn0 0 n0 = ⊤ := by
      apply top_le_iff.mp
      rw [← GRSWald.C_zero_top]
      exact lintegral_mono fun z => ENat.toENNReal_le.mpr
        (le_crossTime fun n h1 h2 => crossTime_le (by omega) h2)
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
