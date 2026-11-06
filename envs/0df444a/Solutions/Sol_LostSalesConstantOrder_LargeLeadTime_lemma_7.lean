-- Prove2me | solution 1 for LostSalesConstantOrder.LargeLeadTime.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T11:43:45.717476+00:00
-- url     : https://prove2.me/submissions/b5715be2-53f4-4e03-8b46-b1847c868709

import Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_lemma_6

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LSCOL7

open CappedBaseStock LostSalesConstantOrder.LargeLeadTime

lemma measurable_nat_max {Ω : Type*} [MeasurableSpace Ω] {f g : Ω → ℕ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (fun p => max (f p) (g p)) :=
  (measurable_of_countable (fun q : ℕ × ℕ => max q.1 q.2)).comp (hf.prodMk hg)

lemma measurable_filter_sup {Ω : Type*} [MeasurableSpace Ω] (P : Ω → ℕ → Prop)
    [∀ p, DecidablePred (P p)] (hP : ∀ j, MeasurableSet {p | P p j}) (s : Finset ℕ) :
    Measurable (fun p => (s.filter (P p)).sup id) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have heq : (fun p => ((insert a s).filter (P p)).sup id) =
        fun p => if P p a then max a ((s.filter (P p)).sup id) else (s.filter (P p)).sup id := by
      funext p
      rw [Finset.filter_insert]
      split_ifs with h
      · rw [Finset.sup_insert]; rfl
      · rfl
    rw [heq]
    exact Measurable.ite (hP a) (measurable_nat_max measurable_const ih) ih

lemma measurable_wTerm (r : ℝ≥0) (k j : ℕ) :
    Measurable (fun p : ℝ≥0 × DemandPath => wTerm r k p.1 p.2 j) := by
  unfold wTerm
  by_cases h : j = k
  · simp only [h, if_true]
    exact ((measurable_walk r k).comp measurable_snd).add measurable_fst.coe_nnreal_real
  · simp only [h, if_false, add_zero]
    exact (measurable_walk r j).comp measurable_snd

lemma measurable_Wk (r : ℝ≥0) (k : ℕ) :
    Measurable (fun p : ℝ≥0 × DemandPath => Wk r k p.1 p.2) := by
  unfold Wk
  exact Finset.measurable_range_sup'' (f := fun j (p : ℝ≥0 × DemandPath) => wTerm r k p.1 p.2 j)
    (fun j _ => measurable_wTerm r k j)

lemma measurable_ik (r : ℝ≥0) (k : ℕ) :
    Measurable (fun p : ℝ≥0 × DemandPath => ik r k p.1 p.2) := by
  unfold ik
  exact measurable_filter_sup (fun (p : ℝ≥0 × DemandPath) (j : ℕ) => wTerm r k p.1 p.2 j = Wk r k p.1 p.2)
    (fun j => measurableSet_eq_fun (measurable_wTerm r k j) (measurable_Wk r k))
    (Finset.range (k + 1))

lemma ik_le (r : ℝ≥0) (k : ℕ) (I₁ : ℝ≥0) (d : DemandPath) : ik r k I₁ d ≤ k := by
  classical
  unfold ik
  apply Finset.sup_le
  intro j hj
  have := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
  simp only [id]
  omega

/-- composing a measurable family indexed by `ℕ` with a measurable `ℕ`-valued function -/
lemma measurable_comp_nat {Ω : Type*} [MeasurableSpace Ω] (G : ℕ → Ω → ℝ)
    (hG : ∀ n, Measurable (G n)) {N : Ω → ℕ} (hN : Measurable N) :
    Measurable (fun p => G (N p) p) := by
  have : Measurable (fun q : ℕ × Ω => G q.1 q.2) :=
    measurable_from_prod_countable_right (fun n => hG n)
  exact this.comp (hN.prodMk measurable_id)

lemma integrable_coord_prod (P : DemandLaw) (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (i : ℕ) :
    Integrable (fun p : ℝ≥0 × DemandPath => (p.2 i : ℝ)) (μ.prod (demandPathLaw P)) := by
  have h := Measure.infinitePi_map_eval (fun _ : ℕ => P.law) i
  have hi : Integrable (fun e : ℝ≥0 => (e : ℝ)) ((demandPathLaw P).map (fun d => d i)) := by
    unfold demandPathLaw; rw [h]; exact P.finiteMean
  have := (integrable_map_measure (μ := demandPathLaw P)
    measurable_id.coe_nnreal_real.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).1 hi
  exact this.comp_snd μ

lemma sum_D_le (d : DemandPath) {n k : ℕ} (hn : n ≤ k) :
    ∑ i ∈ Finset.Icc 1 n, (d (i - 1) : ℝ) ≤ ∑ i ∈ Finset.Icc 1 k, (d (i - 1) : ℝ) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hn)
    (fun _ _ _ => NNReal.coe_nonneg _)

lemma sum_x_le {L : ℕ} (x : Fin L → ℝ≥0) {n k : ℕ} (hn : n ≤ k) :
    ∑ i ∈ Finset.Icc (k + 1 - n) k, (slot x (i - 1) : ℝ) ≤
      ∑ i ∈ Finset.Icc 1 k, (slot x (i - 1) : ℝ) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by omega) le_rfl)
    (fun _ _ _ => NNReal.coe_nonneg _)

lemma Vk_bounds {L : ℕ} (x : Fin L → ℝ≥0) (I : ℝ≥0) (k : ℕ) (hk : 1 ≤ k) (d : DemandPath) :
    0 ≤ Vk x I k d ∧ Vk x I k d ≤ ∑ i ∈ Finset.Icc 1 k, (slot x (i - 1) : ℝ) + I := by
  constructor
  · refine le_trans ?_ (Finset.le_sup' (vTerm x I k d) (Finset.mem_range.2 (by omega : 0 < k + 1)))
    unfold vTerm
    have h0 : Finset.Icc (k + 1 - 0) k = ∅ := by
      ext i; simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
    rw [h0]
    simp only [Finset.sum_empty, Finset.Icc_self, zero_sub]
    split_ifs <;> simp
  · refine Finset.sup'_le _ _ (fun j hj => ?_)
    unfold vTerm
    have h1 := sum_x_le x (n := j) (k := k) (by have := Finset.mem_range.1 hj; omega)
    have h2 : 0 ≤ ∑ i ∈ Finset.Icc 1 j, (d (i - 1) : ℝ) :=
      Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _)
    have h3 : (if j = k then (I : ℝ) else 0) ≤ I := by
      split_ifs <;> simp
    linarith

lemma pointwise {L : ℕ} (x : Fin L → ℝ≥0) (I : ℝ≥0) (r : ℝ≥0) (k : ℕ) (I₁ : ℝ≥0)
    (d : DemandPath) :
    ((ik r k I₁ d : ℝ) * (r : ℝ) - ∑ i ∈ Finset.Icc 1 (ik r k I₁ d), (d (i - 1) : ℝ)) +
      ∑ i ∈ Finset.Icc (k + 1 - ik r k I₁ d) k, (slot x (i - 1) : ℝ) -
      (r : ℝ) * (ik r k I₁ d : ℝ) ≤ Vk x I k d := by
  refine le_trans ?_ (Finset.le_sup' (vTerm x I k d)
    (Finset.mem_range.2 (Nat.lt_succ_of_le (ik_le r k I₁ d))))
  unfold vTerm
  have h3 : (0 : ℝ) ≤ (if ik r k I₁ d = k then (I : ℝ) else 0) := by
    split_ifs <;> simp
  nlinarith

theorem main (P : DemandLaw) (prm : Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (π : AdmissiblePolicy) (hπ : OrdersBounded P π (Qlevel P prm))
    (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (hmin : IsWindowMinimizer P prm x I) (t₀ : ℕ) :
    ENNReal.ofReal
        (prm.h *
            ((∑ k ∈ Finset.Icc 1 prm.L,
                ∫ p, ((ik (rStar x) k p.1 p.2 : ℝ) * (rStar x : ℝ) -
                  ∑ i ∈ Finset.Icc 1 (ik (rStar x) k p.1 p.2), (p.2 (i - 1) : ℝ)) ∂((lawSupWalk P (rStar x)).prod (demandPathLaw P))) +
              (∑ k ∈ Finset.Icc 1 prm.L,
                ∫ p, ∑ i ∈ Finset.Icc (k + 1 - ik (rStar x) k p.1 p.2) k, (slot x (i - 1) : ℝ) ∂((lawSupWalk P (rStar x)).prod (demandPathLaw P))) -
              (rStar x : ℝ) * ∑ k ∈ Finset.Icc 1 prm.L, ∫ p, (ik (rStar x) k p.1 p.2 : ℝ) ∂((lawSupWalk P (rStar x)).prod (demandPathLaw P))) +
          prm.p * ((∫ d, (endInventory prm x I d : ℝ) ∂demandPathLaw P) -
            I + prm.L * mean P - ∑ i, (x i : ℝ))) ≤
      costWindow P prm π t₀ := by
  refine le_trans ?_ (lemma_6 P prm h3 hnd π hπ x I hmin t₀)
  apply ENNReal.ofReal_le_ofReal
  have hh := prm.holding_pos
  set r := rStar x
  set μ := (lawSupWalk P r).prod (demandPathLaw P) with hμ
  have : IsProbabilityMeasure (lawSupWalk P r) :=
    Measure.isProbabilityMeasure_map (measurable_supWalk r).ennreal_toNNReal.aemeasurable
  have hik := measurable_ik r
  -- the three integrands, for fixed k
  have key : ∀ k ∈ Finset.Icc 1 prm.L,
      (∫ p, ((ik r k p.1 p.2 : ℝ) * (r : ℝ) -
          ∑ i ∈ Finset.Icc 1 (ik r k p.1 p.2), (p.2 (i - 1) : ℝ)) ∂μ) +
        (∫ p, ∑ i ∈ Finset.Icc (k + 1 - ik r k p.1 p.2) k, (slot x (i - 1) : ℝ) ∂μ) -
        (r : ℝ) * ∫ p, (ik r k p.1 p.2 : ℝ) ∂μ ≤ ∫ d, Vk x I k d ∂demandPathLaw P := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    -- measurability
    have m3 : Measurable (fun p : ℝ≥0 × DemandPath => (ik r k p.1 p.2 : ℝ)) :=
      measurable_of_countable (fun n : ℕ => (n : ℝ)) |>.comp (hik k)
    have mD : Measurable (fun p : ℝ≥0 × DemandPath =>
        ∑ i ∈ Finset.Icc 1 (ik r k p.1 p.2), (p.2 (i - 1) : ℝ)) :=
      measurable_comp_nat (fun n p => ∑ i ∈ Finset.Icc 1 n, (p.2 (i - 1) : ℝ))
        (fun n => by fun_prop) (hik k)
    have m2 : Measurable (fun p : ℝ≥0 × DemandPath =>
        ∑ i ∈ Finset.Icc (k + 1 - ik r k p.1 p.2) k, (slot x (i - 1) : ℝ)) :=
      measurable_comp_nat (fun n _ => ∑ i ∈ Finset.Icc (k + 1 - n) k, (slot x (i - 1) : ℝ))
        (fun n => measurable_const) (hik k)
    -- integrability
    have iSum : Integrable (fun p : ℝ≥0 × DemandPath =>
        ∑ i ∈ Finset.Icc 1 k, (p.2 (i - 1) : ℝ)) μ :=
      integrable_finsetSum _ (fun i _ => integrable_coord_prod P _ (i - 1))
    have i3 : Integrable (fun p : ℝ≥0 × DemandPath => (ik r k p.1 p.2 : ℝ)) μ := by
      refine Integrable.mono' (integrable_const (k : ℝ)) m3.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun p => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast ik_le r k p.1 p.2
    have iD : Integrable (fun p : ℝ≥0 × DemandPath =>
        ∑ i ∈ Finset.Icc 1 (ik r k p.1 p.2), (p.2 (i - 1) : ℝ)) μ := by
      refine Integrable.mono' iSum mD.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun p => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _))]
      exact sum_D_le p.2 (ik_le r k p.1 p.2)
    have i2 : Integrable (fun p : ℝ≥0 × DemandPath =>
        ∑ i ∈ Finset.Icc (k + 1 - ik r k p.1 p.2) k, (slot x (i - 1) : ℝ)) μ := by
      refine Integrable.mono' (integrable_const (∑ i ∈ Finset.Icc 1 k, (slot x (i - 1) : ℝ)))
        m2.aestronglyMeasurable (Filter.Eventually.of_forall (fun p => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _))]
      exact sum_x_le x (ik_le r k p.1 p.2)
    have i1 : Integrable (fun p : ℝ≥0 × DemandPath => (ik r k p.1 p.2 : ℝ) * (r : ℝ) -
        ∑ i ∈ Finset.Icc 1 (ik r k p.1 p.2), (p.2 (i - 1) : ℝ)) μ :=
      (i3.mul_const _).sub iD
    have mV : Measurable (fun d : DemandPath => Vk x I k d) := by
      unfold Vk
      refine Finset.measurable_range_sup'' (f := fun j d => vTerm x I k d j) (fun j _ => ?_)
      unfold vTerm
      fun_prop
    have iV : Integrable (fun d : DemandPath => Vk x I k d) (demandPathLaw P) := by
      refine Integrable.mono' (integrable_const (∑ i ∈ Finset.Icc 1 k, (slot x (i - 1) : ℝ) + I))
        mV.aestronglyMeasurable (Filter.Eventually.of_forall (fun d => ?_))
      obtain ⟨h0, h1⟩ := Vk_bounds x I k hk1 d
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1
    have hVprod : ∫ d, Vk x I k d ∂demandPathLaw P = ∫ p, Vk x I k p.2 ∂μ := by
      rw [hμ, integral_fun_snd]
      simp
    have i12 : Integrable (fun p : ℝ≥0 × DemandPath => ((ik r k p.1 p.2 : ℝ) * (r : ℝ) -
        ∑ i ∈ Finset.Icc 1 (ik r k p.1 p.2), (p.2 (i - 1) : ℝ)) +
        ∑ i ∈ Finset.Icc (k + 1 - ik r k p.1 p.2) k, (slot x (i - 1) : ℝ)) μ := i1.add i2
    have i3' : Integrable (fun p : ℝ≥0 × DemandPath => (r : ℝ) * (ik r k p.1 p.2 : ℝ)) μ :=
      i3.const_mul _
    rw [hVprod, ← integral_const_mul, ← integral_add i1 i2, ← integral_sub i12 i3']
    refine integral_mono (i12.sub i3') (iV.comp_snd _) (fun p => ?_)
    exact pointwise x I r k p.1 p.2
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  nlinarith

end LSCOL7

open LostSalesConstantOrder.LargeLeadTime in
theorem solution (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (π : CappedBaseStock.AdmissiblePolicy) (hπ : OrdersBounded P π (Qlevel P prm))
    (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (hmin : IsWindowMinimizer P prm x I) (t₀ : ℕ) :
    ENNReal.ofReal
        (prm.h *
            ((∑ k ∈ Finset.Icc 1 prm.L,
                ∫ p, ((ik (rStar x) k p.1 p.2 : ℝ) * (rStar x : ℝ) -
                  ∑ i ∈ Finset.Icc 1 (ik (rStar x) k p.1 p.2), (p.2 (i - 1) : ℝ)) ∂((lawSupWalk P (rStar x)).prod (CappedBaseStock.demandPathLaw P))) +
              (∑ k ∈ Finset.Icc 1 prm.L,
                ∫ p, ∑ i ∈ Finset.Icc (k + 1 - ik (rStar x) k p.1 p.2) k, (slot x (i - 1) : ℝ) ∂((lawSupWalk P (rStar x)).prod (CappedBaseStock.demandPathLaw P))) -
              (rStar x : ℝ) * ∑ k ∈ Finset.Icc 1 prm.L, ∫ p, (ik (rStar x) k p.1 p.2 : ℝ) ∂((lawSupWalk P (rStar x)).prod (CappedBaseStock.demandPathLaw P))) +
          prm.p * ((∫ d, (endInventory prm x I d : ℝ) ∂CappedBaseStock.demandPathLaw P) -
            I + prm.L * CappedBaseStock.mean P - ∑ i, (x i : ℝ))) ≤
      costWindow P prm π t₀ :=
  LSCOL7.main P prm h3 hnd π hπ x I hmin t₀
