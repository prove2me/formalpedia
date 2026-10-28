-- Prove2me | solution 1 for GreedyRS.EFG.theorem3_liminf_at_level
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T10:42:25.150092+00:00
-- url     : https://prove2.me/submissions/f1f469f3-1372-4773-a8a6-d76280f013c9

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting
import Theorems.Thm_GreedyRS_EFG_lemma3_argmin_finite
import Theorems.Thm_GreedyRS_EFG_eq5_2_boundary_crossing

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

namespace GRSRow
open GreedyRS.Greedy

noncomputable def sd (v : ℕ → ℝ≥0) (i : ℕ) : ℝ := Real.sqrt (v i)

noncomputable def row {Ω : Type*} (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ) (i : ℕ)
    (ω : Ω) : ℕ → ℝ := fun j => (X i j ω - μ i) / sd v i

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℕ → ℝ} {v : ℕ → ℝ≥0}
  {X : ℕ → ℕ → Ω → ℝ}

lemma sd_pos (hv : ∀ i, 0 < v i) (i : ℕ) : 0 < sd v i :=
  Real.sqrt_pos.mpr (by exact_mod_cast hv i)

lemma measurable_row (hX : NormalArray P μ v X) (i : ℕ) : Measurable (row μ v X i) :=
  measurable_pi_lambda _ (fun j => ((hX.meas i j).sub_const _).div_const _)

lemma map_entry (hX : NormalArray P μ v X) (hv : ∀ i, 0 < v i) (i j : ℕ) :
    P.map (fun ω => (X i j ω - μ i) / sd v i) = gaussianReal 0 1 := by
  have : (fun ω => (X i j ω - μ i) / sd v i) = (fun y => y / sd v i) ∘ (fun y => y - μ i) ∘ X i j := by
    funext ω; rfl
  rw [this, ← Measure.map_map (g := fun y => y / sd v i) (f := (fun y => y - μ i) ∘ X i j) (by fun_prop)
      ((hX.meas i j).sub_const _),
    ← Measure.map_map (g := fun y => y - μ i) (f := X i j) (by fun_prop) (hX.meas i j),
    hX.law, gaussianReal_map_sub_const, gaussianReal_map_div_const]
  congr 1
  · simp
  · ext
    have h1 : (0 : ℝ) < v i := by exact_mod_cast hv i
    simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_one, sd]
    rw [Real.sq_sqrt h1.le, div_self h1.ne']

lemma iIndep_entries (hX : NormalArray P μ v X) (i : ℕ) :
    iIndepFun (fun j ω => (X i j ω - μ i) / sd v i) P := by
  have h1 := hX.indep.precomp (g := fun j : ℕ => (i, j)) (Prod.mk_right_injective i)
  exact h1.comp (fun _ y => (y - μ i) / sd v i) (fun _ => by fun_prop)

lemma map_row (hX : NormalArray P μ v X) (hv : ∀ i, 0 < v i) (i : ℕ) :
    P.map (row μ v X i) = stdNormalSeq := by
  have := (iIndep_entries hX i).map_fun_eq_infinitePi_map
    (fun j => ((hX.meas i j).sub_const _).div_const _)
  unfold row stdNormalSeq
  rw [this]
  congr 1
  funext j
  exact map_entry hX hv i j

lemma indep_rows (hX : NormalArray P μ v X) {i i' : ℕ} (h : i ≠ i') :
    IndepFun (row μ v X i) (row μ v X i') P := by
  have hind := (iIndepFun_iff_iIndep (fun _ => inferInstance) _ P).mp hX.indep
  have hdis : Disjoint ({p : ℕ × ℕ | p.1 = i}) ({p : ℕ × ℕ | p.1 = i'}) := by
    rw [Set.disjoint_left]
    intro p hp hp'
    exact h (hp.symm.trans hp')
  have hI := indep_iSup_of_disjoint (fun p => (hX.meas p.1 p.2).comap_le) hind hdis
  rw [IndepFun_iff_Indep]
  have hle : ∀ k : ℕ, MeasurableSpace.comap (row μ v X k) inferInstance ≤
      ⨆ p ∈ ({p : ℕ × ℕ | p.1 = k}), MeasurableSpace.comap (fun ω => X p.1 p.2 ω) inferInstance := by
    intro k
    set mS := ⨆ p ∈ ({p : ℕ × ℕ | p.1 = k}),
        MeasurableSpace.comap (fun ω => X p.1 p.2 ω) (inferInstance : MeasurableSpace ℝ) with hmS
    have hm : ∀ j, Measurable[mS] (X k j) := by
      intro j
      have h0 : Measurable[MeasurableSpace.comap (fun ω => X (k, j).1 (k, j).2 ω) inferInstance]
          (X k j) := comap_measurable _
      exact h0.mono (le_iSup₂ (f := fun (p : ℕ × ℕ) (_ : p ∈ ({p : ℕ × ℕ | p.1 = k})) =>
        MeasurableSpace.comap (fun ω => X p.1 p.2 ω) inferInstance) (k, j) rfl) le_rfl
    have hrow : Measurable[mS] (row μ v X k) :=
      @measurable_pi_lambda Ω ℕ (fun _ => ℝ) mS _ _ (fun j => ((hm j).sub_const _).div_const _)
    exact measurable_iff_comap_le.mp hrow
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hI (hle i)) (hle i')

end GRSRow

namespace GRSRow
open GreedyRS.Greedy

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℕ → ℝ} {v : ℕ → ℝ≥0}
  {X : ℕ → ℕ → Ω → ℝ}

lemma runMean_eq (ω : Ω) (i n : ℕ) (hn : n ≠ 0) (hsd : sd v i ≠ 0) :
    runMean (fun i j => X i j ω) i n = μ i + sd v i * zbar (row μ v X i ω) n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  unfold runMean zbar row
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

lemma argminFrom_eq (hv : ∀ i, 0 < v i) (ω : Ω) (n0 : ℕ) (hn0 : 1 ≤ n0) :
    argminFrom (runMean (fun i j => X i j ω) 0) n0 = argminFrom (zbar (row μ v X 0 ω)) n0 := by
  have hsd := sd_pos hv 0
  have key : ∀ m n, n0 ≤ m → n0 ≤ n → (runMean (fun i j => X i j ω) 0 m ≤ runMean (fun i j => X i j ω) 0 n
      ↔ zbar (row μ v X 0 ω) m ≤ zbar (row μ v X 0 ω) n) := by
    intro m n hm hn
    rw [runMean_eq (μ := μ) ω 0 m (by omega) hsd.ne', runMean_eq (μ := μ) ω 0 n (by omega) hsd.ne']
    constructor
    · intro h; exact le_of_mul_le_mul_left (by linarith) hsd
    · intro h; have := mul_le_mul_of_nonneg_left h hsd.le; linarith
  unfold argminFrom
  refine iInf_congr fun m => iInf_congr_Prop ?_ fun _ => rfl
  constructor
  · rintro ⟨hm, h⟩; exact ⟨hm, fun n hn => (key m n hm hn).1 (h n hn)⟩
  · rintro ⟨hm, h⟩; exact ⟨hm, fun n hn => (key m n hm hn).2 (h n hn)⟩

end GRSRow

open GreedyRS.Greedy GRSHelp GRSRow in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ)
    (hX : GreedyRS.Greedy.NormalArray P μ v X) (hv : ∀ i, 0 < v i)
    (γ σbar : ℝ) (hγ : 0 < γ) (hσbar : 0 < σbar)
    (hgap : ∀ i, 1 ≤ i → μ i ≤ μ 0 - γ) (hvar : ∀ i, (v i : ℝ) ≤ σbar ^ 2)
    (n0 : ℕ) (hn0 : 1 ≤ n0) (ng : ℝ) (γ1 : ℝ) (hγ1 : γ1 ∈ Set.Ioo 0 γ)
    (hC : GreedyRS.Greedy.Cn0 ((γ - γ1) / σbar) n0 < ENNReal.ofReal (n0 + ng)) :
    P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) n0 (μ 0 - γ1)} ≤
      Filter.liminf (fun k : ℕ => GreedyRS.Greedy.pcs P X k n0 ⌊((n0 : ℝ) + ng) * k⌋₊) Filter.atTop := by
  set x : ℝ := (γ - γ1) / σbar with hxdef
  have hx : 0 < x := div_pos (by linarith [hγ1.2]) hσbar
  have hσx : σbar * x = γ - γ1 := by rw [hxdef]; field_simp
  have hCtop : Cn0 x n0 ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hC le_top)
  -- the real-valued crossing time and its SLLN
  set cT : (ℕ → ℝ) → ℝ := fun z => ((crossTime x n0 z : ℕ∞) : ℝ≥0∞).toReal with hcT
  have hcTm : Measurable cT := ENNReal.measurable_toReal.comp (measurable_crossTime_enn x n0)
  have hint_std : Integrable cT stdNormalSeq :=
    integrable_toReal_of_lintegral_ne_top (measurable_crossTime_enn x n0).aemeasurable hCtop
  set Y : ℕ → Ω → ℝ := fun m ω => cT (row μ v X (m + 1) ω) with hY
  have hYm : ∀ m, Measurable (Y m) := fun m => hcTm.comp (measurable_row hX (m + 1))
  have hmapY : ∀ m, P.map (Y m) = stdNormalSeq.map cT := by
    intro m
    rw [show Y m = cT ∘ row μ v X (m + 1) from rfl, ← Measure.map_map hcTm (measurable_row hX _),
      map_row hX hv]
  have hint : Integrable (Y 0) P := by
    have := (integrable_map_measure hcTm.aestronglyMeasurable
      (measurable_row hX 1).aemeasurable).mp (by rw [map_row hX hv]; exact hint_std)
    exact this
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i =>
    ⟨(hYm i).aemeasurable, (hYm 0).aemeasurable, by rw [hmapY, hmapY]⟩
  have hindep : Pairwise (Function.onFun (fun f g => IndepFun f g P) Y) := by
    intro i j hij
    exact (indep_rows hX (by omega : i + 1 ≠ j + 1)).comp hcTm hcTm
  have hslln := strong_law_ae_real Y hint hindep hident
  have hmean : P[Y 0] = (Cn0 x n0).toReal := by
    show ∫ ω, cT (row μ v X 1 ω) ∂P = _
    rw [← integral_map (measurable_row hX 1).aemeasurable
      hcTm.aestronglyMeasurable, map_row hX hv]
    unfold Cn0
    rw [integral_toReal (measurable_crossTime_enn x n0).aemeasurable
      (ae_lt_top (measurable_crossTime_enn x n0) hCtop)]
  rw [hmean] at hslln
  -- finiteness of the crossing times
  have hfin : ∀ᵐ ω ∂P, ∀ i, crossTime x n0 (row μ v X i ω) < ⊤ := by
    rw [ae_all_iff]
    intro i
    have h1 : ∀ᵐ z ∂stdNormalSeq, ((crossTime x n0 z : ℕ∞) : ℝ≥0∞) < ⊤ :=
      ae_lt_top (measurable_crossTime_enn x n0) hCtop
    rw [← map_row hX hv i] at h1
    filter_upwards [ae_of_ae_map (measurable_row hX i).aemeasurable h1] with ω hω
    exact ENat.toENNReal_lt_top.mp hω
  -- argmin finite (Lemma 3)
  have hamin : ∀ᵐ ω ∂P, argminFrom (runMean (fun i j => X i j ω) 0) n0 < ⊤ := by
    have h1 := GreedyRS.EFG.lemma3_argmin_finite n0 hn0
    rw [← map_row hX hv 0] at h1
    filter_upwards [ae_of_ae_map (measurable_row hX 0).aemeasurable h1] with ω hω
    rw [argminFrom_eq (μ := μ) hv ω n0 hn0]; exact hω
  -- pathwise comparison N_i(boundary) ≤ Ñ_i(x)
  have hpath : ∀ ω, AboveFrom (runMean (fun i j => X i j ω) 0) n0 (μ 0 - γ1) → ∀ i, 1 ≤ i →
      crossBelow (runMean (fun i j => X i j ω) i) (boundary (runMean (fun i j => X i j ω) 0) n0) n0
        ≤ crossTime x n0 (row μ v X i ω) := by
    intro ω hA i hi
    rcases eq_or_ne (crossTime x n0 (row μ v X i ω)) ⊤ with h | h
    · rw [h]; exact le_top
    obtain ⟨n, hn, h1, h2⟩ := crossTime_spec (lt_top_iff_ne_top.mpr h)
    rw [hn]
    apply iInf₂_le n
    refine ⟨h1, ?_⟩
    have hsd := sd_pos hv i
    have hsdle : sd v i ≤ σbar := by
      unfold sd
      calc Real.sqrt (v i) ≤ Real.sqrt (σbar ^ 2) := Real.sqrt_le_sqrt (hvar i)
        _ = σbar := Real.sqrt_sq hσbar.le
    rw [runMean_eq (μ := μ) ω i n (by omega) hsd.ne']
    have e1 : sd v i * zbar (row μ v X i ω) n < sd v i * x := mul_lt_mul_of_pos_left h2 hsd
    have e2 : sd v i * x ≤ σbar * x := mul_le_mul_of_nonneg_right hsdle hx.le
    have e3 := hgap i hi
    have e4 := hA.2
    unfold boundary
    linarith
  -- assembly
  set c' : ℝ := (n0 : ℝ) + ng with hc'
  set m' : ℝ := (Cn0 x n0).toReal with hm'
  have hm'c : m' < c' := ENNReal.toReal_lt_of_lt_ofReal hC
  have hm'0 : 0 ≤ m' := ENNReal.toReal_nonneg
  set ε : ℝ := (c' - m') / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set tot : ℕ → Ω → ℕ∞ := fun k ω =>
    (∑ i ∈ Finset.Ico 1 k, crossBelow (runMean (fun i j => X i j ω) i)
        (boundary (runMean (fun i j => X i j ω) 0) n0) n0) +
      argminFrom (runMean (fun i j => X i j ω) 0) n0 with htot
  set D : ℕ → Set Ω := fun K => {ω | ∀ k, K ≤ k → tot k ω ≤ (⌊c' * k⌋₊ : ℕ∞)} with hD
  have hDmono : Monotone D := fun K K' hKK ω hω k hk => hω k (hKK.trans hk)
  have hcover : {ω | AboveFrom (runMean (fun i j => X i j ω) 0) n0 (μ 0 - γ1)} ≤ᵐ[P] ⋃ K, D K := by
    filter_upwards [hfin, hslln, hamin] with ω hfω hcω haω
    intro hAω
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt haω)
    obtain ⟨N1, hN1⟩ := eventually_atTop.mp ((tendsto_order.1 hcω).2 (m' + ε) (by linarith))
    obtain ⟨N2, hN2⟩ := exists_nat_ge ((a : ℝ) / ε)
    have haN2 : (a : ℝ) ≤ ε * N2 := by rw [div_le_iff₀ hεpos] at hN2; linarith
    refine Set.mem_iUnion.2 ⟨N1 + N2 + 1, ?_⟩
    intro k hk
    set T : ℕ → ℕ := fun i => (crossTime x n0 (row μ v X i ω)).toNat with hT
    have hTi : ∀ i, crossTime x n0 (row μ v X i ω) = (T i : ℕ∞) := fun i =>
      (ENat.coe_toNat (ne_top_of_lt (hfω i))).symm
    have hYT : ∀ i, Y i ω = (T (i + 1) : ℝ) := by
      intro i
      simp only [hY, hcT]
      rw [hTi (i + 1)]
      simp
    have hsumT : (∑ i ∈ Finset.Ico 1 k, (T i : ℝ)) = ∑ i ∈ Finset.range (k - 1), Y i ω := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hYT, add_comm]
    have hS : ∑ i ∈ Finset.range (k - 1), Y i ω ≤ (m' + ε) * (k - 1 : ℕ) := by
      rcases Nat.eq_zero_or_pos (k - 1) with h0 | hpos
      · rw [h0]; simp
      · have := hN1 (k - 1) (by omega)
        have hpos' : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hpos
        rw [div_lt_iff₀ hpos'] at this
        linarith
    have hk1 : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
    have hN2k : (N2 : ℝ) ≤ k := by exact_mod_cast (show N2 ≤ k by omega)
    have hreal : ((∑ i ∈ Finset.Ico 1 k, T i) + a : ℕ) ≤ c' * k := by
      push_cast
      rw [hsumT]
      have : (m' + ε) * ((k - 1 : ℕ) : ℝ) ≤ (m' + ε) * k :=
        mul_le_mul_of_nonneg_left hk1 (by linarith)
      have : ε * (N2 : ℝ) ≤ ε * k := mul_le_mul_of_nonneg_left hN2k hεpos.le
      have : c' = m' + 2 * ε := by rw [hε]; ring
      nlinarith
    have hnat : (∑ i ∈ Finset.Ico 1 k, T i) + a ≤ ⌊c' * k⌋₊ := Nat.le_floor hreal
    calc tot k ω ≤ (∑ i ∈ Finset.Ico 1 k, (T i : ℕ∞)) + (a : ℕ∞) := by
          simp only [htot]
          rw [ha]
          gcongr with i hi
          rw [← hTi i]
          exact hpath ω hAω i (Finset.mem_Ico.mp hi).1
      _ = (((∑ i ∈ Finset.Ico 1 k, T i) + a : ℕ) : ℕ∞) := by push_cast; rfl
      _ ≤ (⌊c' * k⌋₊ : ℕ∞) := by exact_mod_cast hnat
  calc P {ω | AboveFrom (runMean (fun i j => X i j ω) 0) n0 (μ 0 - γ1)} ≤ P (⋃ K, D K) :=
        measure_mono_ae hcover
    _ = ⨆ K, P (D K) := hDmono.measure_iUnion
    _ ≤ _ := by
        refine iSup_le fun K => le_liminf_of_le (by isBoundedDefault) ?_
        refine eventually_atTop.2 ⟨K, fun k hk => ?_⟩
        refine le_trans (measure_mono (t := {ω | tot k ω ≤ (⌊c' * k⌋₊ : ℕ∞)})
          fun ω hω => hω k hk) ?_
        exact GreedyRS.EFG.eq5_2_boundary_crossing P X k n0 _ hn0
