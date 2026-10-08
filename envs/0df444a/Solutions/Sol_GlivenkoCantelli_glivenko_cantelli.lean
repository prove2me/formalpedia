-- Prove2me | solution 1 for GlivenkoCantelli.glivenko_cantelli
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:17:46.528571+00:00
-- url     : https://prove2.me/submissions/4aa7f2e9-0ab6-4d24-84ce-1ca25b9b8afc

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology

namespace GCAux

/-- SLLN for the indicator of a measurable set. -/
lemma slln_set {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (p : ℝ → Prop) [DecidablePred p] (hs : MeasurableSet {y | p y}) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (((Finset.range n).filter (fun i => p (X i ω))).card : ℝ) / n)
      atTop (𝓝 ((P.map (X 0)).real {y | p y})) := by
  set g : ℝ → ℝ := fun y => if p y then 1 else 0 with hgdef
  have hgi : g = {y | p y}.indicator (fun _ => (1 : ℝ)) := by
    funext y; simp [hgdef, Set.indicator_apply]
  have hg : Measurable g := by rw [hgi]; exact measurable_const.indicator hs
  have hint : Integrable (g ∘ X 0) P := by
    refine (integrable_const (1 : ℝ)).mono' (hg.comp (hX 0)).aestronglyMeasurable
      (ae_of_all _ (fun ω => ?_))
    simp only [Function.comp_apply, g]
    by_cases h : p (X 0 ω) <;> simp [h]
  have hind : Pairwise fun i j => (g ∘ X i) ⟂ᵢ[P] (g ∘ X j) := by
    intro i j hij
    exact (hindep.comp (fun _ => g) (fun _ => hg)).indepFun hij
  have hid : ∀ i, IdentDistrib (g ∘ X i) (g ∘ X 0) P P := fun i => (hident i).comp hg
  have h := strong_law_ae (μ := P) (fun i => g ∘ X i) hint hind hid
  have hE : (∫ ω, (g ∘ X 0) ω ∂P) = (P.map (X 0)).real {y | p y} := by
    have := integral_map (μ := P) (hX 0).aemeasurable hg.aestronglyMeasurable
    simp only [Function.comp_apply]
    rw [← this, hgi]
    exact integral_indicator_one hs
  filter_upwards [h] with ω hω
  rw [hE] at hω
  refine hω.congr (fun n => ?_)
  simp only [Function.comp_apply, g, Finset.sum_boole, smul_eq_mul]
  rw [inv_mul_eq_div]

/-- quantile facts -/
lemma q_bdd (μ : Measure ℝ) [IsProbabilityMeasure μ] {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    BddBelow {x | t ≤ cdf μ x} ∧ {x | t ≤ cdf μ x}.Nonempty := by
  constructor
  · obtain ⟨a, ha⟩ := Filter.eventually_atBot.mp
      ((tendsto_cdf_atBot μ).eventually (gt_mem_nhds ht0))
    refine ⟨a, fun x hx => ?_⟩
    by_contra hxa
    push Not at hxa
    have := ha x hxa.le
    simp only [Set.mem_setOf_eq] at hx
    linarith
  · obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp
      ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds ht1))
    exact ⟨a, (ha a le_rfl).le⟩

lemma q_le (μ : Measure ℝ) [IsProbabilityMeasure μ] {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {x : ℝ} (hx : t ≤ cdf μ x) : sInf {x | t ≤ cdf μ x} ≤ x :=
  csInf_le (q_bdd μ ht0 ht1).1 hx

lemma q_ge (μ : Measure ℝ) [IsProbabilityMeasure μ] {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    t ≤ cdf μ (sInf {x | t ≤ cdf μ x}) := by
  set q := sInf {x | t ≤ cdf μ x}
  obtain ⟨hb, hne⟩ := q_bdd μ ht0 ht1
  have hc : Tendsto (cdf μ) (𝓝[>] q) (𝓝 (cdf μ q)) :=
    ((cdf μ).right_continuous q).mono Set.Ioi_subset_Ici_self
  refine ge_of_tendsto hc (eventually_nhdsWithin_of_forall (fun y hy => ?_))
  obtain ⟨b, hbs, hby⟩ := (csInf_lt_iff hb hne).mp hy
  exact le_trans hbs ((cdf μ).mono hby.le)

lemma q_Iio (μ : Measure ℝ) [IsProbabilityMeasure μ] {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    μ.real (Set.Iio (sInf {x | t ≤ cdf μ x})) ≤ t := by
  set q := sInf {x | t ≤ cdf μ x}
  have h1 := (cdf μ).measure_Iio (tendsto_cdf_atBot μ) q
  rw [measure_cdf] at h1
  have hl : Function.leftLim (cdf μ) q ≤ t := by
    refine le_of_tendsto ((cdf μ).mono.tendsto_leftLim q)
      (eventually_nhdsWithin_of_forall (fun y hy => ?_))
    by_contra hc
    push Not at hc
    have := q_le μ ht0 ht1 hc.le
    exact absurd hy (not_lt.mpr this)
  rw [measureReal_def, h1, sub_zero]
  rcases le_total 0 (Function.leftLim (cdf μ) q) with h | h
  · rw [ENNReal.toReal_ofReal h]; exact hl
  · rw [ENNReal.ofReal_of_nonpos h]; simp; exact ht0.le

lemma low_split (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (m : ℕ) (hm : 1 ≤ m) :
    y ≤ 1 / m ∨ ∃ j : ℕ, 1 ≤ j ∧ j < m ∧ (j : ℝ) / m ≤ y ∧ y ≤ ((j : ℝ) + 1) / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set k := ⌊y * m⌋₊ with hk
  have hk1 : (k : ℝ) ≤ y * m := Nat.floor_le (by positivity)
  have hk2 : y * m < k + 1 := Nat.lt_floor_add_one _
  by_cases hk0 : k = 0
  · left
    rw [hk0] at hk2
    rw [le_div_iff₀ hm']
    push_cast at hk2
    linarith
  by_cases hkm : k < m
  · right
    refine ⟨k, Nat.one_le_iff_ne_zero.mpr hk0, hkm, ?_, ?_⟩
    · rw [div_le_iff₀ hm']; exact hk1
    · rw [le_div_iff₀ hm']; exact hk2.le
  · push Not at hkm
    have hkm' : (m : ℝ) ≤ k := by exact_mod_cast hkm
    have hy : y = 1 := by nlinarith
    by_cases hm1 : m = 1
    · left; subst hm1; simp [hy]
    · right
      refine ⟨m - 1, by omega, by omega, ?_, ?_⟩
      · rw [div_le_iff₀ hm', hy]
        have : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
          rw [Nat.cast_sub hm]; simp
        rw [this]; linarith
      · rw [le_div_iff₀ hm', hy]
        have : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
          rw [Nat.cast_sub hm]; simp
        rw [this]; linarith

lemma up_split (y : ℝ) (hy0 : 0 ≤ y) (m : ℕ) (hm : 1 ≤ m) :
    1 - 1 / m ≤ y ∨ ∃ j : ℕ, 1 ≤ j ∧ j < m ∧ y < (j : ℝ) / m ∧ (j : ℝ) / m ≤ y + 1 / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set k := ⌊y * m⌋₊ with hk
  have hk1 : (k : ℝ) ≤ y * m := Nat.floor_le (by positivity)
  have hk2 : y * m < k + 1 := Nat.lt_floor_add_one _
  by_cases hkm : k + 1 < m
  · right
    refine ⟨k + 1, by omega, hkm, ?_, ?_⟩
    · rw [lt_div_iff₀ hm']; push_cast; exact hk2
    · rw [div_le_iff₀ hm', add_mul, div_mul_cancel₀ _ hm'.ne']; push_cast; linarith
  · left
    push Not at hkm
    have : (m : ℝ) ≤ k + 1 := by exact_mod_cast hkm
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hm']
    nlinarith

end GCAux

open MeasureTheory ProbabilityTheory Filter Topology in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => ⨆ x : ℝ,
        |(((Finset.range n).filter (fun i => X i ω ≤ x)).card : ℝ) / n - cdf (P.map (X 0)) x|)
      atTop (𝓝 0) := by
  have : IsProbabilityMeasure (P.map (X 0)) := Measure.isProbabilityMeasure_map (hX 0).aemeasurable
  set μ := P.map (X 0) with hμ
  set F := cdf μ with hF
  let pt : ℕ × ℕ → ℝ := fun k => sInf {x | ((k.2 : ℝ) / k.1) ≤ F x}
  have hA : ∀ᵐ ω ∂P, ∀ k : ℕ × ℕ, Tendsto
      (fun n : ℕ => (((Finset.range n).filter (fun i => X i ω ≤ pt k)).card : ℝ) / n)
      atTop (𝓝 (F (pt k))) := by
    rw [ae_all_iff]
    intro k
    have := GCAux.slln_set P X hX hindep hident (fun y => y ≤ pt k) measurableSet_Iic
    filter_upwards [this] with ω hω
    rw [hF, cdf_eq_real]
    exact hω
  have hB : ∀ᵐ ω ∂P, ∀ k : ℕ × ℕ, Tendsto
      (fun n : ℕ => (((Finset.range n).filter (fun i => X i ω < pt k)).card : ℝ) / n)
      atTop (𝓝 (μ.real (Set.Iio (pt k)))) := by
    rw [ae_all_iff]
    intro k
    have := GCAux.slln_set P X hX hindep hident (fun y => y < pt k) measurableSet_Iio
    filter_upwards [this] with ω hω
    exact hω
  filter_upwards [hA, hB] with ω hAω hBω
  -- notation
  set A : ℕ → ℝ → ℝ := fun n x =>
    (((Finset.range n).filter (fun i => X i ω ≤ x)).card : ℝ) / n with hAdef
  set B : ℕ → ℝ → ℝ := fun n x =>
    (((Finset.range n).filter (fun i => X i ω < x)).card : ℝ) / n with hBdef
  have A_nonneg : ∀ n x, 0 ≤ A n x := fun n x => by positivity
  have A_le_one : ∀ n x, A n x ≤ 1 := fun n x => by
    refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
    exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range n).le
  have A_mono : ∀ n x y, x ≤ y → A n x ≤ A n y := fun n x y hxy => by
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    refine Nat.cast_le.mpr (Finset.card_le_card (fun i hi => ?_))
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.trans hxy⟩
  have AB : ∀ n x y, x < y → A n x ≤ B n y := fun n x y hxy => by
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    refine Nat.cast_le.mpr (Finset.card_le_card (fun i hi => ?_))
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.trans_lt hxy⟩
  have F_nonneg : ∀ x, 0 ≤ F x := fun x => cdf_nonneg μ x
  have F_le_one : ∀ x, F x ≤ 1 := fun x => cdf_le_one μ x
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / ε)
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := lt_trans (by positivity) hm
    exact_mod_cast this
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hinv : 1 / (m : ℝ) < ε / 2 := by
    rw [div_lt_iff₀ hmpos]
    rw [div_lt_iff₀ hε] at hm
    linarith
  set δ := ε / 4 with hδ
  have hδpos : 0 < δ := by positivity
  have hev : ∀ᶠ n in atTop, 1 ≤ n ∧ ∀ j ∈ Finset.range m,
      |A n (pt (m, j)) - F (pt (m, j))| < δ ∧
      |B n (pt (m, j)) - μ.real (Set.Iio (pt (m, j)))| < δ := by
    refine (eventually_ge_atTop 1).and ?_
    rw [eventually_all_finset]
    intro j _
    have h1 := Metric.tendsto_nhds.mp (hAω (m, j)) δ hδpos
    have h2 := Metric.tendsto_nhds.mp (hBω (m, j)) δ hδpos
    filter_upwards [h1, h2] with n hn1 hn2
    exact ⟨hn1, hn2⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨_, hNn⟩ := hN n hn
  have key : ∀ x, |A n x - F x| ≤ 1 / m + δ := by
    intro x
    rw [abs_le]
    constructor
    · -- lower bound: F x - A n x ≤ 1/m + δ
      rcases GCAux.low_split (F x) (F_nonneg x) (F_le_one x) m hm1 with h | ⟨j, hj1, hjm, hjl, hju⟩
      · linarith [A_nonneg n x]
      · have ht0 : (0 : ℝ) < (j : ℝ) / m := by
          have : (0 : ℝ) < j := by exact_mod_cast hj1
          positivity
        have ht1 : (j : ℝ) / m < 1 := by
          rw [div_lt_one hmpos]; exact_mod_cast hjm
        have hq : pt (m, j) ≤ x := GCAux.q_le μ ht0 ht1 hjl
        have hFq : (j : ℝ) / m ≤ F (pt (m, j)) := GCAux.q_ge μ ht0 ht1
        have hj := (hNn j (Finset.mem_range.mpr hjm)).1
        rw [abs_lt] at hj
        have hmono := A_mono n _ _ hq
        have : ((j : ℝ) + 1) / m = (j : ℝ) / m + 1 / m := by ring
        linarith
    · -- upper bound: A n x - F x ≤ 1/m + δ
      rcases GCAux.up_split (F x) (F_nonneg x) m hm1 with h | ⟨j, hj1, hjm, hjl, hju⟩
      · linarith [A_le_one n x]
      · have ht0 : (0 : ℝ) < (j : ℝ) / m := by
          have : (0 : ℝ) < j := by exact_mod_cast hj1
          positivity
        have ht1 : (j : ℝ) / m < 1 := by
          rw [div_lt_one hmpos]; exact_mod_cast hjm
        have hq : x < pt (m, j) := by
          by_contra hc
          push Not at hc
          have := (F.mono hc)
          have := GCAux.q_ge μ ht0 ht1
          linarith
        have hLq : μ.real (Set.Iio (pt (m, j))) ≤ (j : ℝ) / m := GCAux.q_Iio μ ht0 ht1
        have hj := (hNn j (Finset.mem_range.mpr hjm)).2
        rw [abs_lt] at hj
        have hab := AB n _ _ hq
        linarith
  have hsup : (⨆ x : ℝ, |A n x - F x|) ≤ 1 / m + δ := ciSup_le key
  have hsup0 : 0 ≤ (⨆ x : ℝ, |A n x - F x|) := Real.iSup_nonneg (fun x => abs_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsup0]
  linarith
