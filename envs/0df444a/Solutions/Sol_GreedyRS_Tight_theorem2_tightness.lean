-- Prove2me | solution 1 for GreedyRS.Tight.theorem2_tightness
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T10:32:56.211199+00:00
-- url     : https://prove2.me/submissions/5d642708-bb3c-463f-a496-8ea0583522ac

import Mathlib
import Definitions.Def_GreedyRS_Tight_Setting
import Theorems.Thm_GreedyRS_Tight_theorem1_sccv
import Theorems.Thm_GreedyRS_Tight_ec1_6_liminf_pics
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace G2Sol
open GreedyRS.Greedy

variable {Ω : Type*} [MeasurableSpace Ω]

lemma meas_runMean_nat (x : Ω → ℕ → ℕ → ℝ) (hx : ∀ i j, Measurable fun ω => x ω i j)
    (i : ℕ) (n : Ω → ℕ) (hn : Measurable n) :
    Measurable fun ω => runMean (x ω) i (n ω) := by
  have h2 : Measurable fun p : Ω × ℕ => runMean (x p.1) i p.2 := by
    apply measurable_from_prod_countable_left
    intro m
    show Measurable fun ω => (∑ j ∈ Finset.range m, x ω i j) / (m : ℝ)
    exact (Finset.measurable_sum (Finset.range m) fun j _ => hx i j).div_const _
  exact h2.comp (measurable_id.prodMk hn)

lemma meas_leader (k : ℕ) (x : Ω → ℕ → ℕ → ℝ) (hx : ∀ i j, Measurable fun ω => x ω i j)
    (s : Ω → ℕ → ℕ) (hs : ∀ i, Measurable fun ω => s ω i) :
    Measurable fun ω => leader k (x ω) (s ω) := by
  classical
  by_cases hk : 0 < k
  · have hr : ∀ i, Measurable fun ω => runMean (x ω) i (s ω i) := fun i =>
      meas_runMean_nat x hx i _ (hs i)
    apply measurable_to_countable'
    intro l
    set A : ℕ → ℕ → Set Ω := fun j l => {ω | runMean (x ω) j (s ω j) ≤ runMean (x ω) l (s ω l)}
      with hA
    have hAm : ∀ j l, MeasurableSet (A j l) := fun j l => measurableSet_le (hr j) (hr l)
    have hset : (fun ω => leader k (x ω) (s ω)) ⁻¹' {l} =
        {ω | l < k} ∩ ((⋂ j ∈ Finset.range k, A j l) ∩
          ⋂ j ∈ Finset.range l, ({ω | j < k} ∩ ⋂ j' ∈ Finset.range k, A j' j)ᶜ) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, leader, hk, dif_pos, Set.mem_inter_iff,
        Set.mem_iInter, Set.mem_compl_iff, Finset.mem_range, hA]
      rw [Nat.find_eq_iff]
      exact and_assoc
    rw [hset]
    refine MeasurableSet.inter (MeasurableSet.const _) (MeasurableSet.inter ?_ ?_)
    · exact MeasurableSet.biInter (Finset.range k).countable_toSet fun j _ => hAm j l
    · refine MeasurableSet.biInter (Finset.range l).countable_toSet fun j _ => ?_
      exact (MeasurableSet.inter (MeasurableSet.const _)
        (MeasurableSet.biInter (Finset.range k).countable_toSet fun j' _ => hAm j' j)).compl
  · have : ∀ ω, leader k (x ω) (s ω) = 0 := fun ω => by simp [leader, hk]
    simp_rw [this]
    exact measurable_const

lemma meas_efgSizes (k n0 : ℕ) (x : Ω → ℕ → ℕ → ℝ) (hx : ∀ i j, Measurable fun ω => x ω i j)
    (m : ℕ) : ∀ i, Measurable fun ω => efgSizes k n0 (x ω) m i := by
  induction m with
  | zero => intro i; simp [efgSizes]
  | succ m ih =>
    intro i
    have hl := meas_leader k x hx (fun ω => efgSizes k n0 (x ω) m) ih
    have hval : Measurable fun ω =>
        efgSizes k n0 (x ω) m (leader k (x ω) (efgSizes k n0 (x ω) m)) := by
      have h2 : Measurable fun p : Ω × ℕ => efgSizes k n0 (x p.1) m p.2 :=
        measurable_from_prod_countable_left fun j => ih j
      exact h2.comp (measurable_id.prodMk hl)
    simp only [efgSizes, Function.update_apply]
    refine Measurable.ite ?_ (hval.add_const 1) (ih i)
    exact measurableSet_eq_fun measurable_const hl

lemma meas_select_set (k B : ℕ) (X : ℕ → ℕ → Ω → ℝ) (hX : ∀ i j, Measurable (X i j)) :
    MeasurableSet {ω | greedySelect k B (fun i j => X i j ω) = 0} := by
  have hx : ∀ i j, Measurable fun ω => (fun i j => X i j ω) i j := hX
  have := meas_leader k (fun ω => fun i j => X i j ω) hx
    (fun ω => efgSizes k 1 (fun i j => X i j ω) (B - 1 * k))
    (meas_efgSizes k 1 _ hx _)
  exact this (MeasurableSet.singleton 0)


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

lemma runMean_slln (P : Measure Ω) [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (X : ℕ → ℕ → Ω → ℝ) (hX : NormalArray P μ v X) :
    ∀ᵐ ω ∂P, Tendsto (fun n => runMean (fun i j => X i j ω) 0 n) atTop (𝓝 (μ 0)) := by
  have hint : Integrable (X 0 0) P := by
    have h1 : Integrable id (P.map (X 0 0)) := by
      rw [hX.law 0 0]
      exact (memLp_id_gaussianReal 1).integrable le_rfl
    exact (integrable_map_measure aestronglyMeasurable_id (hX.meas 0 0).aemeasurable).1 h1
  have hindep : Pairwise (Function.onFun (fun f g => IndepFun f g P) (fun j => X 0 j)) := by
    intro i j hij
    exact (row_indep P μ v X hX).indepFun hij
  have hident : ∀ i, IdentDistrib (X 0 i) (X 0 0) P P := by
    intro i
    refine ⟨(hX.meas 0 i).aemeasurable, (hX.meas 0 0).aemeasurable, ?_⟩
    rw [hX.law 0 i, hX.law 0 0]
  have hmean : P[X 0 0] = μ 0 := by
    have : ∫ x, x ∂(P.map (X 0 0)) = ∫ ω, X 0 0 ω ∂P :=
      integral_map (hX.meas 0 0).aemeasurable aestronglyMeasurable_id
    rw [← this, hX.law 0 0, integral_id_gaussianReal]
  filter_upwards [strong_law_ae (fun j => X 0 j) hint hindep hident] with ω hω
  rw [hmean] at hω
  refine hω.congr fun n => ?_
  simp only [runMean, smul_eq_mul]
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


lemma squeeze_aux (f g : ℕ → ℝ≥0∞) (p q : ℝ≥0∞) (hfg : ∀ k, f k = 1 - g k)
    (hg1 : ∀ k, g k ≤ 1) (hq1 : q ≤ 1)
    (hp : p ≤ liminf f atTop) (hq : q ≤ liminf g atTop) (hpq : p = 1 - q) :
    Tendsto f atTop (𝓝 p) := by
  refine tendsto_order.2 ⟨fun b hb => eventually_lt_of_lt_liminf (hb.trans_le hp), fun b hb => ?_⟩
  by_cases hb1 : 1 < b
  · exact Eventually.of_forall fun k => (hfg k ▸ tsub_le_self : f k ≤ 1).trans_lt hb1
  · push Not at hb1
    have h1 : 1 < b + q := by
      have : (1 - q) + q < b + q := ENNReal.add_lt_add_right (ne_top_of_le_ne_top ENNReal.one_ne_top hq1)
        (hpq ▸ hb)
      rwa [tsub_add_cancel_of_le hq1] at this
    have h2 : 1 - b < q := ENNReal.sub_lt_of_lt_add hb1 (by rwa [add_comm])
    filter_upwards [eventually_lt_of_lt_liminf (h2.trans_le hq)] with k hk
    rw [hfg k]
    have : 1 < b + g k := by
      have h3 : (1 - b) + b < g k + b :=
        ENNReal.add_lt_add_right (ne_top_of_le_ne_top ENNReal.one_ne_top hb1) hk
      rwa [tsub_add_cancel_of_le hb1, add_comm] at h3
    exact ENNReal.sub_lt_of_lt_add (hg1 k) this

end G2Sol

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ) (hX : GreedyRS.Greedy.NormalArray P μ v X)
    (γ : ℝ) (hγ : 0 < γ) (hslip : ∀ i, 1 ≤ i → μ i = μ 0 - γ)
    (w : ℝ≥0) (hw : 0 < w) (hcv : ∀ i, v i = w)
    (c : ℝ) (hc : GreedyRS.Greedy.Cfun (γ / Real.sqrt w) < c) :
    (∃ γ0 ∈ Set.Ioo 0 γ, GreedyRS.Greedy.Cfun ((γ - γ0) / Real.sqrt w) = c) ∧
    ∀ γ0 ∈ Set.Ioo 0 γ, GreedyRS.Greedy.Cfun ((γ - γ0) / Real.sqrt w) = c →
      Tendsto (fun k : ℕ => GreedyRS.Greedy.pcs P X k 1 ⌊c * k⌋₊) atTop
          (𝓝 (P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)})) ∧
      P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)}
          = ENNReal.ofReal (1 / GreedyRS.Greedy.Cfun (γ0 / Real.sqrt w)) := by
  obtain ⟨hex, h1⟩ := GreedyRS.Tight.theorem1_sccv P μ v X hX γ hγ hslip w hw hcv c hc
  refine ⟨hex, fun γ0 hγ0 hC0 => ?_⟩
  obtain ⟨hlow, heq, -⟩ := h1 γ0 hγ0 hC0
  have hpics := GreedyRS.Tight.ec1_6_liminf_pics P μ v X hX γ hγ hslip w hw hcv c hc γ0 hγ0 hC0
  refine ⟨?_, heq⟩
  set a := μ 0 - γ0 with ha
  have haμ : a < μ 0 := by have := hγ0.1; linarith
  set A := {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) 1 a}
    with hA
  set E := {ω | ∃ n : ℕ, 1 ≤ n ∧ GreedyRS.Greedy.runMean (fun i j => X i j ω) 0 n < a} with hE
  have hrm : ∀ n, Measurable fun ω => GreedyRS.Greedy.runMean (fun i j => X i j ω) 0 n := by
    intro n
    exact G2Sol.meas_runMean_nat (fun ω i j => X i j ω) (fun i j => hX.meas i j) 0
      (fun _ => n) measurable_const
  have hEm : MeasurableSet E := by
    have : E = ⋃ n, ({ω | 1 ≤ n} ∩ {ω | GreedyRS.Greedy.runMean (fun i j => X i j ω) 0 n < a}) := by
      ext ω; simp [hE]
    rw [this]
    exact MeasurableSet.iUnion fun n =>
      (MeasurableSet.const _).inter (measurableSet_lt (hrm n) measurable_const)
  have hv0 : v 0 ≠ 0 := by rw [hcv 0]; exact hw.ne'
  have hAE : P A = 1 - P E := by
    rw [← prob_compl_eq_one_sub hEm]
    apply le_antisymm
    · apply measure_mono
      intro ω hω
      simp only [hA, Set.mem_setOf_eq] at hω
      simp only [hE, Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_and, not_lt]
      intro n hn
      obtain ⟨hb, hlt⟩ := hω
      have := ciInf_le hb (n - 1)
      have h' : 1 + (n - 1) = n := by omega
      rw [h'] at this
      linarith
    · let N1 := ⋃ n : ℕ, ({ω | 1 ≤ n} ∩ {ω | GreedyRS.Greedy.runMean (fun i j => X i j ω) 0 n = a})
      let N2 := {ω | ¬ Tendsto (fun n => GreedyRS.Greedy.runMean (fun i j => X i j ω) 0 n) atTop
        (𝓝 (μ 0))}
      have hN1 : P N1 = 0 := by
        refine measure_iUnion_null fun n => ?_
        by_cases hn : 1 ≤ n
        · exact measure_mono_null Set.inter_subset_right
            (G2Sol.runMean_atom P μ v X hX hv0 a n hn)
        · have : {ω : Ω | 1 ≤ n} = ∅ := by ext; simp [hn]
          rw [this, Set.empty_inter, measure_empty]
      have hN2 : P N2 = 0 := by
        have := G2Sol.runMean_slln P μ v X hX
        rw [ae_iff] at this
        exact this
      have hsub : Eᶜ ⊆ A ∪ (N1 ∪ N2) := by
        intro ω hω
        simp only [hE, Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_and, not_lt] at hω
        by_cases hAω : ω ∈ A
        · exact Or.inl hAω
        by_cases hT : Tendsto (fun n => GreedyRS.Greedy.runMean (fun i j => X i j ω) 0 n) atTop
            (𝓝 (μ 0))
        · obtain ⟨n, hn, hy⟩ := G2Sol.attain_of_tendsto _ (μ 0) a hT haμ hω hAω
          exact Or.inr (Or.inl (Set.mem_iUnion.2 ⟨n, hn, hy⟩))
        · exact Or.inr (Or.inr hT)
      calc P Eᶜ ≤ P (A ∪ (N1 ∪ N2)) := measure_mono hsub
        _ ≤ P A + (P N1 + P N2) := (measure_union_le _ _).trans (add_le_add_right (measure_union_le _ _) _)
        _ = P A := by rw [hN1, hN2]; simp
  have hfg : ∀ k : ℕ, GreedyRS.Greedy.pcs P X k 1 ⌊c * k⌋₊ =
      1 - P {ω | GreedyRS.Greedy.greedySelect k ⌊c * k⌋₊ (fun i j => X i j ω) ≠ 0} := by
    intro k
    have hm := G2Sol.meas_select_set k ⌊c * k⌋₊ X hX.meas
    have hc' : {ω | GreedyRS.Greedy.greedySelect k ⌊c * k⌋₊ (fun i j => X i j ω) ≠ 0} =
        {ω | GreedyRS.Greedy.greedySelect k ⌊c * k⌋₊ (fun i j => X i j ω) = 0}ᶜ := by
      ext; simp
    rw [hc', prob_compl_eq_one_sub hm, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
    rfl
  exact G2Sol.squeeze_aux _ _ _ _ hfg (fun k => prob_le_one) prob_le_one hlow hpics hAE
