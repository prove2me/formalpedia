-- Prove2me | solution 1 for KallMayerSLP.Bonferroni.bonferroni_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:24:05.709133+00:00
-- url     : https://prove2.me/submissions/b2b4f700-5bc6-44dd-844c-3b675836885c

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_binomialMoment
import Definitions.Def_KallMayerSLP_Bonferroni_occurrenceCount

set_option autoImplicit false

open MeasureTheory

open KallMayerSLP.Bonferroni

/-- Partial alternating sums of binomial coefficients:
`∑_{j=1}^m (-1)^(j-1) C(n+1, j) = 1 - (-1)^m C(n, m)`. -/
private lemma partial_alt_sum (n m : ℕ) :
    ∑ j ∈ Finset.Icc 1 m, (-1 : ℝ) ^ (j - 1) * ((n + 1).choose j : ℝ) =
      1 - (-1 : ℝ) ^ m * (n.choose m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.choose_succ_succ]
    push_cast
    simp only [pow_succ]
    ring

private lemma partial_alt_sum_zero (m : ℕ) :
    ∑ j ∈ Finset.Icc 1 m, (-1 : ℝ) ^ (j - 1) * ((0 : ℕ).choose j : ℝ) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_Icc] at hj
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

/-- The pointwise counting function `g_j(ω) = ∑_{|I|=j} 1_{⋂_I B}(ω)`. -/
private noncomputable def g {Ω : Type*} {r : ℕ} (B : Fin r → Set Ω) (j : ℕ) (ω : Ω) : ℝ :=
  ∑ I ∈ Finset.powersetCard j (Finset.univ : Finset (Fin r)),
    (⋂ i ∈ I, B i).indicator (fun _ => (1 : ℝ)) ω

private lemma g_eq {Ω : Type*} {r : ℕ} (B : Fin r → Set Ω) (j : ℕ) (ω : Ω) :
    g B j ω = ((occurrenceCount B ω).choose j : ℝ) := by
  classical
  unfold g occurrenceCount
  simp only [Set.indicator_apply]
  rw [Finset.sum_boole, ← Finset.card_powersetCard]
  congr 2
  ext I
  simp only [Finset.mem_filter, Finset.mem_powersetCard, true_and,
    Set.mem_iInter, Finset.subset_iff, Finset.mem_univ]
  tauto

private lemma g_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i)) (j : ℕ) :
    Integrable (g B j) μ := by
  unfold g
  refine integrable_finsetSum _ fun I _ => ?_
  exact (integrable_const (1 : ℝ)).indicator (Finset.measurableSet_biInter I fun i _ => hB i)

private lemma bm_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i)) (j : ℕ) :
    binomialMoment μ B j = ∫ ω, g B j ω ∂μ := by
  unfold binomialMoment g
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun I _ => ?_
    rw [← integral_indicator_one (Finset.measurableSet_biInter I fun i _ => hB i)]
    rfl
  · intro I _
    exact (integrable_const (1 : ℝ)).indicator (Finset.measurableSet_biInter I fun i _ => hB i)

private lemma alt_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i)) (M : ℕ) :
    ∑ j ∈ Finset.Icc 1 M, (-1 : ℝ) ^ (j - 1) * binomialMoment μ B j =
      ∫ ω, ∑ j ∈ Finset.Icc 1 M, (-1 : ℝ) ^ (j - 1) * g B j ω ∂μ := by
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [bm_eq μ B hB j, integral_const_mul]
  · intro j _
    exact (g_integrable μ B hB j).const_mul _

private lemma alt_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i)) (M : ℕ) :
    Integrable (fun ω => ∑ j ∈ Finset.Icc 1 M, (-1 : ℝ) ^ (j - 1) * g B j ω) μ :=
  integrable_finsetSum _ fun j _ => (g_integrable μ B hB j).const_mul _

private lemma occ_set_eq {Ω : Type*} {r : ℕ} (B : Fin r → Set Ω) :
    {ω | 1 ≤ occurrenceCount B ω} = ⋃ i, B i := by
  classical
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, occurrenceCount, Nat.one_le_iff_ne_zero, ne_eq,
    Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies, not_forall,
    not_not]

private lemma prob_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i)) :
    μ.real {ω | 1 ≤ occurrenceCount B ω} =
      ∫ ω, {ω | 1 ≤ occurrenceCount B ω}.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
  have hs : MeasurableSet {ω | 1 ≤ occurrenceCount B ω} := by
    rw [occ_set_eq]; exact MeasurableSet.iUnion hB
  rw [← integral_indicator_one hs]
  rfl

private lemma ind_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i)) :
    Integrable ({ω | 1 ≤ occurrenceCount B ω}.indicator (fun _ => (1 : ℝ))) μ := by
  have hs : MeasurableSet {ω | 1 ≤ occurrenceCount B ω} := by
    rw [occ_set_eq]; exact MeasurableSet.iUnion hB
  exact (integrable_const (1 : ℝ)).indicator hs

/-- Pointwise value of the alternating sum in terms of `ν = occurrenceCount`. -/
private lemma alt_pointwise {Ω : Type*} {r : ℕ} (B : Fin r → Set Ω) (M : ℕ) (ω : Ω) :
    ∑ j ∈ Finset.Icc 1 M, (-1 : ℝ) ^ (j - 1) * g B j ω =
      if occurrenceCount B ω = 0 then 0
      else 1 - (-1 : ℝ) ^ M * ((occurrenceCount B ω - 1).choose M : ℝ) := by
  simp only [g_eq]
  rcases Nat.eq_zero_or_eq_succ_pred (occurrenceCount B ω) with h | h
  · rw [h, if_pos rfl, partial_alt_sum_zero]
  · rw [h, if_neg (Nat.succ_ne_zero _), partial_alt_sum, Nat.succ_sub_one]

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (hr : 1 ≤ r) (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i)) (m : ℕ) (hm : Even m) (hmr : m < r) :
    ∑ j ∈ Finset.Icc 1 m, (-1 : ℝ) ^ (j - 1) * binomialMoment μ B j ≤
        μ.real {ω | 1 ≤ occurrenceCount B ω} ∧
      μ.real {ω | 1 ≤ occurrenceCount B ω} ≤
        ∑ j ∈ Finset.Icc 1 (m + 1), (-1 : ℝ) ^ (j - 1) * binomialMoment μ B j := by
  have hm1 : (-1 : ℝ) ^ m = 1 := hm.neg_one_pow
  have hm2 : (-1 : ℝ) ^ (m + 1) = -1 := by rw [pow_succ, hm1]; ring
  rw [alt_eq μ B hB, alt_eq μ B hB, prob_eq μ B hB]
  have hC : ∀ (ω : Ω) (k : ℕ), (0 : ℝ) ≤ ((occurrenceCount B ω - 1).choose k : ℝ) :=
    fun _ _ => Nat.cast_nonneg _
  constructor
  · refine integral_mono (alt_integrable μ B hB m) (ind_integrable μ B hB) fun ω => ?_
    have := hC ω m
    simp only [alt_pointwise, Set.indicator_apply, Set.mem_ofPred_eq, hm1]
    split_ifs <;> first | omega | linarith
  · refine integral_mono (ind_integrable μ B hB) (alt_integrable μ B hB (m + 1)) fun ω => ?_
    have := hC ω (m + 1)
    simp only [alt_pointwise, Set.indicator_apply, Set.mem_ofPred_eq, hm2]
    split_ifs <;> first | omega | linarith
