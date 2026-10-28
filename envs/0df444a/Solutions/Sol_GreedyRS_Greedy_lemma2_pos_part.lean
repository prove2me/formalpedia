-- Prove2me | solution 1 for GreedyRS.Greedy.lemma2_pos_part
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T11:33:57.365689+00:00
-- url     : https://prove2.me/submissions/d23ccf78-bee4-424c-9f2c-042936d4705b

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting
import Theorems.Thm_GreedyRS_Greedy_eq4_3_min_prob
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace G11
open GreedyRS.Greedy

lemma iInf_coe_eq_iff (p : ℕ → Prop) (m : ℕ) :
    (⨅ (n : ℕ) (_ : p n), (n : ℕ∞)) = m ↔ p m ∧ ∀ n, p n → m ≤ n := by
  constructor
  · intro h
    have hle : ∀ n, p n → m ≤ n := by
      intro n hn
      have : (m : ℕ∞) ≤ n := h ▸ iInf₂_le n hn
      exact_mod_cast this
    refine ⟨?_, hle⟩
    by_contra hpm
    have : ((m + 1 : ℕ) : ℕ∞) ≤ ⨅ (n : ℕ) (_ : p n), (n : ℕ∞) := by
      refine le_iInf₂ fun n hn => ?_
      have h1 := hle n hn
      have h2 : n ≠ m := fun h => hpm (h ▸ hn)
      exact_mod_cast (show m + 1 ≤ n by omega)
    rw [h] at this
    have : m + 1 ≤ m := by exact_mod_cast this
    omega
  · rintro ⟨hpm, hle⟩
    apply le_antisymm
    · exact iInf₂_le m hpm
    · exact le_iInf₂ fun n hn => by exact_mod_cast hle n hn

lemma iInf_coe_eq_top_iff (p : ℕ → Prop) :
    (⨅ (n : ℕ) (_ : p n), (n : ℕ∞)) = ⊤ ↔ ∀ n, ¬ p n := by
  simp only [iInf_eq_top, ENat.coe_ne_top, imp_false]

lemma meas_hit {α : Type*} [MeasurableSpace α] (p : α → ℕ → Prop)
    (hp : ∀ n, MeasurableSet {a | p a n}) :
    Measurable fun a => ⨅ (n : ℕ) (_ : p a n), (n : ℕ∞) := by
  apply measurable_to_countable'
  intro N
  induction N using ENat.recTopCoe with
  | top =>
    have : (fun a => ⨅ (n : ℕ) (_ : p a n), (n : ℕ∞)) ⁻¹' {⊤} = ⋂ n, {a | p a n}ᶜ := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_compl_iff]
      rw [iInf_coe_eq_top_iff]; rfl
    rw [this]; exact MeasurableSet.iInter fun n => (hp n).compl
  | coe m =>
    have : (fun a => ⨅ (n : ℕ) (_ : p a n), (n : ℕ∞)) ⁻¹' {(m : ℕ∞)} =
        {a | p a m} ∩ ⋂ n ∈ Finset.range m, {a | p a n}ᶜ := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_compl_iff, Finset.mem_range]
      rw [iInf_coe_eq_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun n hn hpn => ?_⟩
        have := h2 n hpn; omega
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun n hpn => ?_⟩
        by_contra hlt
        exact h2 n (by omega) hpn
    rw [this]
    exact (hp m).inter (MeasurableSet.biInter (Finset.range m).countable_toSet
      fun n _ => (hp n).compl)

lemma meas_crossTime (x : ℝ) : Measurable fun z : ℕ → ℝ => crossTime x 1 z := by
  unfold crossTime
  apply meas_hit (fun z n => 1 ≤ n ∧ zbar z n < x)
  intro n
  show MeasurableSet ({z : ℕ → ℝ | 1 ≤ n} ∩ {z | zbar z n < x})
  refine (MeasurableSet.const _).inter (measurableSet_lt ?_ measurable_const)
  unfold zbar
  exact (Finset.measurable_sum _ fun j _ => measurable_pi_apply j).div_const _

/-- Standardisation of a row turns `crossBelow` of its running mean into `crossTime`. -/
lemma crossBelow_eq_crossTime (x : ℕ → ℝ) (m L σ : ℝ) (hσ : 0 < σ) :
    crossBelow (fun n => (∑ j ∈ Finset.range n, x j) / n) L 1 =
      crossTime ((L - m) / σ) 1 (fun j => (x j - m) / σ) := by
  unfold crossBelow crossTime
  refine iInf_congr fun n => iInf_congr_Prop ?_ (fun _ => rfl)
  · constructor
    · rintro ⟨hn, h⟩
      refine ⟨hn, ?_⟩
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      unfold zbar
      rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, div_div, div_lt_div_iff₀ (by positivity) hσ]
      rw [div_lt_iff₀ hn'] at h
      nlinarith
    · rintro ⟨hn, h⟩
      refine ⟨hn, ?_⟩
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      unfold zbar at h
      rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, div_div, div_lt_div_iff₀ (by positivity) hσ] at h
      rw [div_lt_iff₀ hn']
      nlinarith

lemma gauss_standardize (m : ℝ) (w : ℝ≥0) (hw : 0 < w) :
    (gaussianReal m w).map (fun t => (t - m) / Real.sqrt w) = gaussianReal 0 1 := by
  have hσ : 0 < Real.sqrt w := Real.sqrt_pos.2 (by exact_mod_cast hw)
  have : (fun t => (t - m) / Real.sqrt w) = (fun t => t / Real.sqrt w) ∘ (fun t => t - m) := rfl
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_sub_const,
    gaussianReal_map_div_const]
  congr 1
  · simp
  · ext
    simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_one]
    rw [Real.sq_sqrt (NNReal.coe_nonneg w)]
    exact div_self (by exact_mod_cast hw.ne')

variable {Ω : Type*} [MeasurableSpace Ω]

lemma rows_law (P : Measure Ω) [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (X : ℕ → ℕ → Ω → ℝ) (hX : NormalArray P μ v X) :
    P.map (fun ω i j => X i j ω) =
      Measure.infinitePi (fun i => Measure.infinitePi (fun _ : ℕ => gaussianReal (μ i) (v i))) := by
  have hjm : Measurable (fun ω (p : ℕ × ℕ) => X p.1 p.2 ω) :=
    measurable_pi_lambda _ fun p => hX.meas p.1 p.2
  have hjoint : P.map (fun ω (p : ℕ × ℕ) => X p.1 p.2 ω) =
      Measure.infinitePi (fun p : ℕ × ℕ => gaussianReal (μ p.1) (v p.1)) := by
    have h := hX.indep.map_fun_eq_infinitePi_map (fun p : ℕ × ℕ => hX.meas p.1 p.2)
    rw [h]
    congr 1; ext1 p; exact hX.law p.1 p.2
  have hcomp : (fun ω i j => X i j ω) =
      (MeasurableEquiv.curry ℕ ℕ ℝ) ∘ (fun ω (p : ℕ × ℕ) => X p.1 p.2 ω) := by
    ext ω i j; rfl
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.curry ℕ ℕ ℝ).measurable hjm, hjoint]
  exact Measure.infinitePi_map_curry (fun i (_ : ℕ) => gaussianReal (μ i) (v i))

lemma row_law (P : Measure Ω) [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (X : ℕ → ℕ → Ω → ℝ) (hX : NormalArray P μ v X) (i : ℕ) :
    P.map (fun ω j => X i j ω) = Measure.infinitePi (fun _ : ℕ => gaussianReal (μ i) (v i)) := by
  have hrm : Measurable (fun ω i j => X i j ω) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hX.meas i j
  have : (fun ω j => X i j ω) = (fun f : ℕ → ℕ → ℝ => f i) ∘ (fun ω i j => X i j ω) := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply i) hrm, rows_law P μ v X hX,
    Measure.infinitePi_map_eval]

lemma rows_indep (P : Measure Ω) [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (X : ℕ → ℕ → Ω → ℝ) (hX : NormalArray P μ v X) :
    iIndepFun (fun i ω j => X i j ω) P := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun i => measurable_pi_lambda _ fun j => hX.meas i j)]
  rw [rows_law P μ v X hX]
  congr 1; ext1 i
  exact (row_law P μ v X hX i).symm

end G11

namespace GL2
open GreedyRS.Greedy

variable {Ω : Type*} [MeasurableSpace Ω]

lemma seq_sum_law (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ j, Measurable (Y j)) (hind : iIndepFun Y P) (m : ℝ) (w : ℝ≥0)
    (hlaw : ∀ j, P.map (Y j) = gaussianReal m w) (n : ℕ) :
    P.map (∑ j ∈ Finset.range n, Y j) = gaussianReal (n * m) (n * w) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, CharP.cast_eq_zero, zero_mul,
      gaussianReal_zero_var]
    show P.map (fun _ => (0:ℝ)) = _
    rw [Measure.map_const]; simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hi : IndepFun (∑ j ∈ Finset.range n, Y j) (Y n) P :=
      hind.indepFun_finsetSum_of_notMem hY (by simp)
    rw [gaussianReal_add_gaussianReal_of_indepFun hi ih (hlaw n)]
    congr 1
    · push_cast; ring
    · push_cast; ring

lemma seq_mean_atom (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ j, Measurable (Y j)) (hind : iIndepFun Y P) (m : ℝ) (w : ℝ≥0) (hw : w ≠ 0)
    (hlaw : ∀ j, P.map (Y j) = gaussianReal m w) (a : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    P {ω | (∑ j ∈ Finset.range n, Y j ω) / n = a} = 0 := by
  have hmeas : Measurable (∑ j ∈ Finset.range n, Y j) := by
    have h := Finset.measurable_sum (Finset.range n) (fun j _ => hY j)
    convert h using 1; ext ω; simp
  have hsub : {ω | (∑ j ∈ Finset.range n, Y j ω) / n = a} ⊆
      (∑ j ∈ Finset.range n, Y j) ⁻¹' {n * a} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.sum_apply]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [← hω]; field_simp
  refine measure_mono_null hsub ?_
  rw [← Measure.map_apply hmeas (MeasurableSet.singleton _), seq_sum_law P Y hY hind m w hlaw n]
  have hnv : ((n : ℝ≥0) * w) ≠ 0 := mul_ne_zero (by exact_mod_cast (show n ≠ 0 by omega)) hw
  exact gaussianReal_absolutelyContinuous _ hnv (by simp)

lemma seq_slln (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ j, Measurable (Y j)) (hind : iIndepFun Y P) (m : ℝ) (w : ℝ≥0)
    (hlaw : ∀ j, P.map (Y j) = gaussianReal m w) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, Y j ω) / n) atTop (𝓝 m) := by
  have hint : Integrable (Y 0) P := by
    have h1 : Integrable id (P.map (Y 0)) := by
      rw [hlaw 0]; exact (memLp_id_gaussianReal 1).integrable le_rfl
    exact (integrable_map_measure aestronglyMeasurable_id (hY 0).aemeasurable).1 h1
  have hindep : Pairwise (Function.onFun (fun f g => IndepFun f g P) Y) :=
    fun i j hij => hind.indepFun hij
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i =>
    ⟨(hY i).aemeasurable, (hY 0).aemeasurable, by rw [hlaw i, hlaw 0]⟩
  have hmean : P[Y 0] = m := by
    have : ∫ x, x ∂(P.map (Y 0)) = ∫ ω, Y 0 ω ∂P :=
      integral_map (hY 0).aemeasurable aestronglyMeasurable_id
    rw [← this, hlaw 0, integral_id_gaussianReal]
  filter_upwards [strong_law_ae Y hint hindep hident] with ω hω
  rw [hmean] at hω
  refine hω.congr fun n => ?_
  simp only [smul_eq_mul]
  rw [div_eq_inv_mul]

/-- A real sequence converging to `L` whose values (from index `1`) stay `≥ a` with `a < L`
and whose infimum is not `> a` attains the value `a`. -/
lemma attain_of_tendsto (y : ℕ → ℝ) (L a : ℝ) (hL : Tendsto y atTop (𝓝 L)) (haL : a < L)
    (hge : ∀ n, 1 ≤ n → a ≤ y n) (hnot : ¬ AboveFrom y 1 a) : ∃ n, 1 ≤ n ∧ y n = a := by
  by_contra hcon
  push Not at hcon
  have hgt : ∀ n, 1 ≤ n → a < y n := fun n hn => lt_of_le_of_ne (hge n hn) (fun h => hcon n hn h.symm)
  apply hnot
  have hbdd : BddBelow (Set.range fun n => y (1 + n)) :=
    ⟨a, by rintro _ ⟨n, rfl⟩; exact hge _ (by omega)⟩
  refine ⟨hbdd, ?_⟩
  -- eventually y n > (a + L)/2
  have hev : ∀ᶠ n in atTop, (a + L) / 2 < y n :=
    hL.eventually (lt_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  -- finite minimum over 1..N
  obtain ⟨m0, hm0, hmin⟩ := Finset.exists_min_image (Finset.range (N + 1))
    (fun n => y (1 + n)) ⟨0, by simp⟩
  set b := min (y (1 + m0)) ((a + L) / 2) with hb
  have hab : a < b := lt_min (hgt _ (by omega)) (by linarith)
  have hle : b ≤ ⨅ n, y (1 + n) := by
    refine le_ciInf fun n => ?_
    by_cases hn : n ≤ N
    · exact (min_le_left _ _).trans (hmin n (by simp; omega))
    · exact (min_le_right _ _).trans (hN _ (by omega)).le
  linarith


lemma std_coords :
    (∀ j, Measurable (fun z : ℕ → ℝ => z j)) ∧
    iIndepFun (fun j (z : ℕ → ℝ) => z j) stdNormalSeq ∧
    ∀ j, stdNormalSeq.map (fun z : ℕ → ℝ => z j) = gaussianReal 0 1 := by
  refine ⟨fun j => measurable_pi_apply j, ?_, fun j => ?_⟩
  · unfold stdNormalSeq
    exact iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1) (X := fun _ => id)
      (fun _ => measurable_id)
  · unfold stdNormalSeq
    exact Measure.infinitePi_map_eval _ j

/-- For `x < 0`, `Pr{∀ n ≥ 1, Z̄(n) ≥ x} = Pr{min_{n ≥ 1} Z̄(n) > x}`. -/
lemma weak_eq_strict (x : ℝ) (hx : x < 0) :
    stdNormalSeq {z | crossTime x 1 z = ⊤} = stdNormalSeq {z | AboveFrom (zbar z) 1 x} := by
  haveI : IsProbabilityMeasure stdNormalSeq := by unfold stdNormalSeq; infer_instance
  obtain ⟨hm, hind, hlaw⟩ := std_coords
  have hT : ∀ z, crossTime x 1 z = ⊤ ↔ ∀ n, 1 ≤ n → x ≤ zbar z n := by
    intro z
    unfold crossTime
    rw [G11.iInf_coe_eq_top_iff]
    simp only [not_and, not_lt]
  apply le_antisymm
  · set N1 := ⋃ n : ℕ, ({z : ℕ → ℝ | 1 ≤ n} ∩ {z | zbar z n = x})
    set N2 := {z : ℕ → ℝ | ¬ Tendsto (fun n => zbar z n) atTop (𝓝 0)}
    have hN1 : stdNormalSeq N1 = 0 := by
      refine measure_iUnion_null fun n => ?_
      by_cases hn : 1 ≤ n
      · refine measure_mono_null Set.inter_subset_right ?_
        exact seq_mean_atom stdNormalSeq (fun j z => z j) hm hind 0 1 one_ne_zero hlaw x n hn
      · have : {z : ℕ → ℝ | 1 ≤ n} = ∅ := by ext; simp [hn]
        rw [this, Set.empty_inter, measure_empty]
    have hN2 : stdNormalSeq N2 = 0 := by
      have := seq_slln stdNormalSeq (fun j z => z j) hm hind 0 1 hlaw
      rw [ae_iff] at this
      exact this
    calc stdNormalSeq {z | crossTime x 1 z = ⊤}
        ≤ stdNormalSeq ({z | AboveFrom (zbar z) 1 x} ∪ (N1 ∪ N2)) := by
          apply measure_mono
          intro z hz
          rw [Set.mem_setOf_eq, hT] at hz
          by_cases hA : AboveFrom (zbar z) 1 x
          · exact Or.inl hA
          by_cases ht : Tendsto (fun n => zbar z n) atTop (𝓝 0)
          · obtain ⟨n, hn, he⟩ := attain_of_tendsto (zbar z) 0 x ht hx hz hA
            exact Or.inr (Or.inl (Set.mem_iUnion.2 ⟨n, hn, he⟩))
          · exact Or.inr (Or.inr ht)
      _ ≤ stdNormalSeq {z | AboveFrom (zbar z) 1 x} + (stdNormalSeq N1 + stdNormalSeq N2) :=
          (measure_union_le _ _).trans (add_le_add_right (measure_union_le _ _) _)
      _ = _ := by rw [hN1, hN2]; simp
  · apply measure_mono
    intro z hz
    rw [Set.mem_setOf_eq, hT]
    intro n hn
    obtain ⟨hb, hlt⟩ := hz
    have := ciInf_le hb (n - 1)
    have h' : 1 + (n - 1) = n := by omega
    rw [h'] at this
    linarith

end GL2

namespace GD
open GreedyRS.Greedy

instance : IsProbabilityMeasure stdNormalSeq := by unfold stdNormalSeq; infer_instance

/-- Reindexing the coordinates by an injection preserves `stdNormalSeq`. -/
lemma map_reindex (g : ℕ → ℕ) (hg : g.Injective) :
    stdNormalSeq.map (fun z j => z (g j)) = stdNormalSeq := by
  obtain ⟨hm, hind, hlaw⟩ := GL2.std_coords
  have h1 : iIndepFun (fun j (z : ℕ → ℝ) => z (g j)) stdNormalSeq := hind.precomp hg
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map (fun j => hm (g j))).1 h1]
  conv_rhs => unfold stdNormalSeq
  congr 1; ext1 j
  exact hlaw (g j)

/-- Negating all coordinates preserves `stdNormalSeq`. -/
lemma map_neg : stdNormalSeq.map (fun z j => -z j) = stdNormalSeq := by
  obtain ⟨hm, hind, hlaw⟩ := GL2.std_coords
  have h1 : iIndepFun (fun j (z : ℕ → ℝ) => -z j) stdNormalSeq :=
    hind.comp (fun _ t => -t) (fun _ => measurable_neg)
  have hmn : ∀ j, Measurable (fun z : ℕ → ℝ => -z j) := fun j => (hm j).neg
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map hmn).1 h1]
  conv_rhs => unfold stdNormalSeq
  congr 1; ext1 j
  have : (fun z : ℕ → ℝ => -z j) = (fun t : ℝ => -t) ∘ (fun z : ℕ → ℝ => z j) := rfl
  rw [this, ← Measure.map_map measurable_neg (hm j), hlaw j, gaussianReal_map_neg, neg_zero]

lemma enat_eq_tsum (t : ℕ∞) : (t : ℝ≥0∞) = ∑' n : ℕ, if (n : ℕ∞) < t then 1 else 0 := by
  induction t using ENat.recTopCoe with
  | top =>
    simp only [ENat.coe_lt_top, if_true, ENat.toENNReal_top]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  | coe m =>
    rw [tsum_eq_sum (s := Finset.range m)]
    · rw [Finset.sum_congr rfl (fun n hn => if_pos (by
          have := Finset.mem_range.1 hn; exact_mod_cast this))]
      simp
    · intro n hn
      rw [if_neg]
      have := Finset.mem_range.not.1 hn
      exact_mod_cast not_lt.2 (not_lt.1 this)

lemma lintegral_enat {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℕ∞)
    (hf : Measurable f) :
    ∫⁻ a, (f a : ℝ≥0∞) ∂μ = ∑' n : ℕ, μ {a | (n : ℕ∞) < f a} := by
  simp_rw [enat_eq_tsum]
  rw [lintegral_tsum]
  · refine tsum_congr fun n => ?_
    have hs : MeasurableSet {a | (n : ℕ∞) < f a} := hf (Set.to_countable {s : ℕ∞ | (n : ℕ∞) < s}).measurableSet
    have : (fun a => if (n : ℕ∞) < f a then (1 : ℝ≥0∞) else 0) =
        Set.indicator {a | (n : ℕ∞) < f a} 1 := by
      ext a; simp [Set.indicator_apply]
    rw [this, lintegral_indicator_one hs]
  · intro n
    have hs : MeasurableSet {a | (n : ℕ∞) < f a} := hf (Set.to_countable {s : ℕ∞ | (n : ℕ∞) < s}).measurableSet
    have : (fun a => if (n : ℕ∞) < f a then (1 : ℝ≥0∞) else 0) =
        Set.indicator {a | (n : ℕ∞) < f a} 1 := by
      ext a; simp [Set.indicator_apply]
    rw [this]
    exact (measurable_one.indicator hs).aemeasurable

lemma lt_iInf_coe_iff (p : ℕ → Prop) (n : ℕ) :
    (n : ℕ∞) < ⨅ (k : ℕ) (_ : p k), (k : ℕ∞) ↔ ∀ k, p k → n < k := by
  constructor
  · intro h k hk
    have := lt_of_lt_of_le h (iInf₂_le k hk)
    exact_mod_cast this
  · intro h
    have : ((n + 1 : ℕ) : ℕ∞) ≤ ⨅ (k : ℕ) (_ : p k), (k : ℕ∞) :=
      le_iInf₂ fun k hk => by exact_mod_cast h k hk
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) this

/-- The centred partial sums `T_j(z) = ∑_{i<j} (z_i - x)`. -/
noncomputable def T (x : ℝ) (j : ℕ) (z : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range j, (z i - x)

lemma T_meas (x : ℝ) (j : ℕ) : Measurable (T x j) :=
  Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).sub_const _

lemma zbar_lt_iff (x : ℝ) (z : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m) : zbar z m < x ↔ T x m z < 0 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold zbar T
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, div_lt_iff₀ hm']
  constructor <;> intro h <;> linarith

lemma T_succ (x : ℝ) (j : ℕ) (z : ℕ → ℝ) : T x (j + 1) z = T x j z + (z j - x) := by
  unfold T; rw [Finset.sum_range_succ]

/-- The reversal of the first `n` coordinates. -/
def rev (n : ℕ) (j : ℕ) : ℕ := if j < n then n - 1 - j else j

lemma rev_injective (n : ℕ) : (rev n).Injective := by
  intro a b h
  unfold rev at h
  split_ifs at h with ha hb hb <;> omega

lemma T_rev (x : ℝ) (n : ℕ) (z : ℕ → ℝ) :
    ∀ k ≤ n, T x k (fun j => z (rev n j)) = T x n z - T x (n - k) z := by
  intro k
  induction k with
  | zero => intro _; simp [T]
  | succ k ih =>
    intro hk
    rw [T_succ, ih (by omega)]
    have h1 : n - k = (n - (k + 1)) + 1 := by omega
    rw [h1, T_succ]
    have h2 : rev n k = n - (k + 1) := by unfold rev; rw [if_pos (by omega)]; omega
    rw [h2]
    ring

lemma T_shift (x : ℝ) (n m : ℕ) (z : ℕ → ℝ) :
    T x m (fun j => z (j + n)) = T x (n + m) z - T x n z := by
  unfold T
  rw [Finset.sum_range_add]
  simp only [add_comm]
  ring

end GD

namespace GD
open GreedyRS.Greedy

/-- The σ-algebra of the first `n` coordinates. -/
def past (n : ℕ) : MeasurableSpace (ℕ → ℝ) :=
  ⨆ i ∈ Set.Iio n, MeasurableSpace.comap (fun z : ℕ → ℝ => z i) inferInstance

lemma coord_meas_past (n i : ℕ) (hi : i < n) : Measurable[past n] (fun z : ℕ → ℝ => z i) := by
  intro s hs
  refine le_iSup₂ (f := fun i (_ : i ∈ Set.Iio n) =>
    MeasurableSpace.comap (fun z : ℕ → ℝ => z i) inferInstance) i hi _ ⟨s, hs, rfl⟩

lemma T_meas_past (x : ℝ) (n j : ℕ) (hj : j ≤ n) : Measurable[past n] (T x j) := by
  unfold T
  exact Finset.measurable_sum (m := past n) _ fun i hi =>
    (coord_meas_past n i (by have := Finset.mem_range.1 hi; omega)).sub_const _

lemma L_meas_past (x : ℝ) (n : ℕ) :
    MeasurableSet[past n] {z : ℕ → ℝ | ∀ j < n, T x j z ≤ T x n z} := by
  have : {z : ℕ → ℝ | ∀ j < n, T x j z ≤ T x n z} =
      ⋂ j ∈ Finset.range n, {z | T x j z ≤ T x n z} := by
    ext z; simp
  rw [this]
  exact MeasurableSet.biInter (m := past n) (Finset.range n).countable_toSet fun j hj =>
    measurableSet_le (T_meas_past x n j (by have := Finset.mem_range.1 hj; omega))
      (T_meas_past x n n le_rfl)

/-- The σ-algebra of the coordinates `≥ n`. -/
def future (n : ℕ) : MeasurableSpace (ℕ → ℝ) :=
  ⨆ i ∈ Set.Ici n, MeasurableSpace.comap (fun z : ℕ → ℝ => z i) inferInstance

lemma shift_meas_future (n : ℕ) :
    @Measurable (ℕ → ℝ) (ℕ → ℝ) (future n) MeasurableSpace.pi (fun z j => z (j + n)) := by
  refine @measurable_pi_lambda (ℕ → ℝ) ℕ (fun _ => ℝ) (future n) (fun _ => inferInstance) _ ?_
  intro j s hs
  exact le_iSup₂ (f := fun i (_ : i ∈ Set.Ici n) =>
    MeasurableSpace.comap (fun z : ℕ → ℝ => z i) inferInstance) (j + n)
    (by simp) _ ⟨s, hs, rfl⟩

lemma indep_shift (n : ℕ) (A B : Set (ℕ → ℝ)) (hA : MeasurableSet[past n] A)
    (hB : MeasurableSet B) :
    stdNormalSeq (A ∩ (fun z j => z (j + n)) ⁻¹' B) = stdNormalSeq A * stdNormalSeq B := by
  obtain ⟨hm, hind, -⟩ := GL2.std_coords
  have hiI : iIndep (fun i => MeasurableSpace.comap (fun z : ℕ → ℝ => z i) inferInstance)
      stdNormalSeq := (iIndepFun_iff_iIndep _ _ _).1 hind
  have hle : ∀ i, MeasurableSpace.comap (fun z : ℕ → ℝ => z i) inferInstance ≤
      (inferInstance : MeasurableSpace (ℕ → ℝ)) := fun i => (hm i).comap_le
  have hdisj : Disjoint (Set.Iio n) (Set.Ici n) := by
    rw [Set.disjoint_left]; intro a ha hb
    simp only [Set.mem_Iio] at ha; simp only [Set.mem_Ici] at hb; omega
  have hI := indep_iSup_of_disjoint hle hiI hdisj
  have h2 : MeasurableSet[future n] ((fun (z : ℕ → ℝ) (j : ℕ) => z (j + n)) ⁻¹' B) :=
    shift_meas_future n hB
  rw [(Indep_iff _ _ _).1 hI A _ hA h2]
  congr 1
  have hmeas : Measurable (fun (z : ℕ → ℝ) (j : ℕ) => z (j + n)) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply (j + n)
  rw [← Measure.map_apply hmeas hB, map_reindex (· + n) (add_left_injective n)]

end GD

namespace GD
open GreedyRS.Greedy

lemma T_zero (x : ℝ) (z : ℕ → ℝ) : T x 0 z = 0 := by simp [T]

/-- Ladder duality: `E[Ñ(x)] · Pr{T_m < 0 for all m ≥ 1} = 1` for `x > 0`. -/
theorem duality (x : ℝ) (hx : 0 < x) :
    Cn0 x 1 * stdNormalSeq {w | ∀ m, 1 ≤ m → T x m w < 0} = 1 := by
  set μ := stdNormalSeq with hμ
  set B := {w : ℕ → ℝ | ∀ m, 1 ≤ m → T x m w < 0} with hB
  have hBm : MeasurableSet B := by
    have : B = ⋂ m : ℕ, ({w : ℕ → ℝ | 1 ≤ m}ᶜ ∪ {w | T x m w < 0}) := by
      ext w; simp only [hB, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
      constructor
      · intro h m; by_cases hm : 1 ≤ m
        · exact Or.inr (h m hm)
        · exact Or.inl hm
      · intro h m hm; exact (h m).resolve_left (not_not.2 hm)
    rw [this]
    exact MeasurableSet.iInter fun m => (MeasurableSet.const _).compl.union
      (measurableSet_lt (T_meas x m) measurable_const)
  set L : ℕ → Set (ℕ → ℝ) := fun n => {z | ∀ j < n, T x j z ≤ T x n z} with hL
  have hLm : ∀ n, MeasurableSet (L n) := by
    intro n
    have : L n = ⋂ j ∈ Finset.range n, {z | T x j z ≤ T x n z} := by ext z; simp [hL]
    rw [this]
    exact MeasurableSet.biInter (Finset.range n).countable_toSet fun j _ =>
      measurableSet_le (T_meas x j) (T_meas x n)
  set sh : ℕ → (ℕ → ℝ) → (ℕ → ℝ) := fun n z j => z (j + n) with hsh
  have hshm : ∀ n, Measurable (sh n) := fun n =>
    measurable_pi_lambda _ fun j => measurable_pi_apply (j + n)
  set E : ℕ → Set (ℕ → ℝ) := fun n => L n ∩ (sh n) ⁻¹' B with hE
  have hEm : ∀ n, MeasurableSet (E n) := fun n => (hLm n).inter (hshm n hBm)
  have hEμ : ∀ n, μ (E n) = μ (L n) * μ B := fun n => indep_shift n (L n) B (L_meas_past x n) hBm
  have hshB : ∀ n z, z ∈ (sh n) ⁻¹' B ↔ ∀ m, 1 ≤ m → T x (n + m) z < T x n z := by
    intro n z
    simp only [Set.mem_preimage, hB, Set.mem_setOf_eq, hsh]
    refine forall_congr' fun m => imp_congr_right fun _ => ?_
    rw [T_shift]; constructor <;> intro h <;> linarith
  -- disjointness
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    have key : ∀ n n', n < n' → Disjoint (E n) (E n') := by
      intro n n' hnn'
      rw [Set.disjoint_left]
      rintro z ⟨_, hz1⟩ ⟨hz2, _⟩
      have h1 := (hshB n z).1 hz1 (n' - n) (by omega)
      rw [show n + (n' - n) = n' by omega] at h1
      have h2 := hz2 n hnn'
      linarith
    intro n n' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key n n' h
    · exact (key n' n h).symm
  -- the `E n` cover almost everything
  have hcover : ∀ᵐ z ∂μ, z ∈ ⋃ n, E n := by
    obtain ⟨hm, hind, hlaw⟩ := GL2.std_coords
    filter_upwards [GL2.seq_slln stdNormalSeq (fun j z => z j) hm hind 0 1 hlaw] with z hz
    have hev : ∀ᶠ m : ℕ in atTop, (∑ j ∈ Finset.range m, z j) / m < x / 2 :=
      hz.eventually (gt_mem_nhds (by linarith))
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
    set N := N0 + 1 with hN
    have hneg : ∀ m, N ≤ m → T x m z < 0 := by
      intro m hm
      have hm1 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have h := hN0 m (by omega)
      rw [div_lt_iff₀ hm1] at h
      unfold T
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      nlinarith
    obtain ⟨j0, hj0, hmax⟩ := Finset.exists_max_image (Finset.range N) (fun j => T x j z)
      ⟨0, Finset.mem_range.2 (by omega)⟩
    set M := T x j0 z with hM
    set F := (Finset.range N).filter (fun j => T x j z = M) with hF
    have hFne : F.Nonempty := ⟨j0, by rw [hF, Finset.mem_filter]; exact ⟨hj0, hM.symm⟩⟩
    set n := F.max' hFne with hn
    have hnF : n ∈ F := F.max'_mem hFne
    simp only [hF, Finset.mem_filter, Finset.mem_range] at hnF
    refine Set.mem_iUnion.2 ⟨n, ?_, ?_⟩
    · intro j hj
      rw [hnF.2]
      exact hmax j (Finset.mem_range.2 (by omega))
    · rw [hshB]
      intro m hm
      by_cases hk : n + m < N
      · have hle : T x (n + m) z ≤ M := hmax _ (Finset.mem_range.2 hk)
        rw [hnF.2]
        refine lt_of_le_of_ne hle fun heq => ?_
        have hmem : n + m ∈ F := by simp [hF, hk, heq]
        have := F.le_max' _ hmem
        rw [← hn] at this
        omega
      · have h1 := hneg (n + m) (by omega)
        have h2 : T x 0 z ≤ M := hmax 0 (Finset.mem_range.2 (by omega))
        rw [T_zero] at h2
        rw [hnF.2]
        linarith
  have hU : μ (⋃ n, E n) = 1 := by
    rw [← prob_compl_eq_zero_iff (MeasurableSet.iUnion hEm)]
    rw [ae_iff] at hcover
    exact hcover
  have hsum : ∑' n, μ (E n) = 1 := by
    rw [← measure_iUnion hdisj hEm, hU]
  -- `E[Ñ(x)] = ∑ μ(L n)`
  have hA : ∀ n : ℕ, μ {z | (n : ℕ∞) < crossTime x 1 z} = μ (L n) := by
    intro n
    have hrevm : Measurable (fun (z : ℕ → ℝ) j => z (rev n j)) :=
      measurable_pi_lambda _ fun j => measurable_pi_apply (rev n j)
    have hAm : MeasurableSet {z : ℕ → ℝ | (n : ℕ∞) < crossTime x 1 z} :=
      G11.meas_crossTime x (Set.to_countable {s : ℕ∞ | (n : ℕ∞) < s}).measurableSet
    rw [hμ, ← map_reindex (rev n) (rev_injective n), Measure.map_apply hrevm hAm,
      map_reindex (rev n) (rev_injective n)]
    congr 1
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hL]
    unfold crossTime
    rw [lt_iInf_coe_iff]
    constructor
    · intro h j hj
      have h1 := h (n - j)
      have h2 : ¬ (1 ≤ n - j ∧ zbar (fun i => z (rev n i)) (n - j) < x) := fun hc => by
        have := h1 hc; omega
      rw [zbar_lt_iff x _ _ (by omega), T_rev x n z (n - j) (by omega),
        show n - (n - j) = j by omega] at h2
      push Not at h2
      linarith [h2 (by omega)]
    · intro h k ⟨hk1, hk2⟩
      by_contra hkn
      push Not at hkn
      rw [zbar_lt_iff x _ _ hk1, T_rev x n z k hkn] at hk2
      have := h (n - k) (by omega)
      linarith
  have hC : Cn0 x 1 = ∑' n, μ (L n) := by
    unfold Cn0
    rw [lintegral_enat _ _ (G11.meas_crossTime x)]
    exact tsum_congr hA
  rw [hC, ← ENNReal.tsum_mul_right, ← hsum]
  exact tsum_congr fun n => (hEμ n).symm

end GD

theorem solution (x : ℝ) (hx : 0 < x) :
    GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.crossTime x 1 z < ⊤} = 1 ∧
      GreedyRS.Greedy.Cn0 x 1 = ENNReal.ofReal (GreedyRS.Greedy.Cfun x) := by
  open GreedyRS.Greedy in
  obtain ⟨hm, hind, hlaw⟩ := GL2.std_coords
  have hslln := GL2.seq_slln stdNormalSeq (fun j z => z j) hm hind 0 1 hlaw
  have hT : ∀ (y : ℝ) z, crossTime y 1 z = ⊤ ↔ ∀ n, 1 ≤ n → y ≤ zbar z n := by
    intro y z
    unfold crossTime
    rw [G11.iInf_coe_eq_top_iff]
    simp only [not_and, not_lt]
  constructor
  · -- a.s. finiteness, from the strong law
    have hset : {z : ℕ → ℝ | crossTime x 1 z < ⊤} = {z | crossTime x 1 z = ⊤}ᶜ := by
      ext z; simp [lt_top_iff_ne_top]
    rw [hset, prob_compl_eq_one_sub (show MeasurableSet {z : ℕ → ℝ | crossTime x 1 z = ⊤} from
      G11.meas_crossTime x (MeasurableSet.singleton _))]
    have h0 : stdNormalSeq {z : ℕ → ℝ | crossTime x 1 z = ⊤} = 0 := by
      rw [ae_iff] at hslln
      refine measure_mono_null ?_ hslln
      intro z hz hconv
      rw [Set.mem_setOf_eq, hT] at hz
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hconv.eventually (gt_mem_nhds hx))
      have := hz (N + 1) (by omega)
      have h2 := hN (N + 1) (by omega)
      unfold zbar at this
      linarith
    rw [h0, tsub_zero]
  · -- the mean, via ladder duality and (4.3)
    set B := {w : ℕ → ℝ | ∀ m, 1 ≤ m → GD.T x m w < 0} with hB
    have hBm : MeasurableSet B := by
      have : B = ⋂ m : ℕ, ({w : ℕ → ℝ | 1 ≤ m}ᶜ ∪ {w | GD.T x m w < 0}) := by
        ext w; simp only [hB, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
        constructor
        · intro h m; by_cases hm : 1 ≤ m
          · exact Or.inr (h m hm)
          · exact Or.inl hm
        · intro h m hm; exact (h m).resolve_left (not_not.2 hm)
      rw [this]
      exact MeasurableSet.iInter fun m => (MeasurableSet.const _).compl.union
        (measurableSet_lt (GD.T_meas x m) measurable_const)
    have hnegm : Measurable (fun (z : ℕ → ℝ) (j : ℕ) => -z j) :=
      measurable_pi_lambda _ fun j => (measurable_pi_apply j).neg
    have hzneg : ∀ (z : ℕ → ℝ) m, zbar (fun j => -z j) m = -zbar z m := by
      intro z m; unfold zbar; rw [Finset.sum_neg_distrib, neg_div]
    have hpre : (fun (z : ℕ → ℝ) (j : ℕ) => -z j) ⁻¹' B = {z | ∀ m, 1 ≤ m → -x < zbar z m} := by
      ext z
      simp only [Set.mem_preimage, hB, Set.mem_setOf_eq]
      refine forall_congr' fun m => forall_congr' fun hm => ?_
      rw [← GD.zbar_lt_iff x _ m hm, hzneg]
      constructor <;> intro h <;> linarith
    have hA := (GreedyRS.Greedy.eq4_3_min_prob (-x) (by linarith)).2
    rw [neg_neg] at hA
    have hW := GL2.weak_eq_strict (-x) (by linarith)
    have hq : stdNormalSeq B = ENNReal.ofReal (1 / Cfun x) := by
      rw [← GD.map_neg, Measure.map_apply hnegm hBm, hpre]
      apply le_antisymm
      · rw [← hA, ← hW]
        apply measure_mono
        intro z hz
        rw [Set.mem_setOf_eq, hT]
        intro n hn; exact (hz n hn).le
      · rw [← hA]
        apply measure_mono
        rintro z ⟨hb, hlt⟩ m hm
        have := ciInf_le hb (m - 1)
        rw [show 1 + (m - 1) = m by omega] at this
        linarith
    have hdual := GD.duality x hx
    rw [← hB, hq] at hdual
    have hCpos : 0 < Cfun x := by unfold Cfun; exact Real.exp_pos _
    rw [ENNReal.eq_inv_of_mul_eq_one_left hdual, ← ENNReal.ofReal_inv_of_pos (by positivity),
      one_div, inv_inv]
