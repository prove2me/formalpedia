-- Prove2me | solution 1 for HighDimProb.Concentration.hoeffding_rademacher
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T21:36:10.049599+00:00
-- url     : https://prove2.me/submissions/75772d9c-b7bd-47f8-b5ad-3a1c6053984a

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real

lemma hdpc_ae_mem_pair {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (a b : ℝ) (hab : a ≠ b)
    (h : P.real {ω | Y ω = a} + P.real {ω | Y ω = b} = 1) :
    ∀ᵐ ω ∂P, Y ω = a ∨ Y ω = b := by
  have hA : MeasurableSet {ω | Y ω = a} := hY (measurableSet_singleton a)
  have hB : MeasurableSet {ω | Y ω = b} := hY (measurableSet_singleton b)
  have hdisj : Disjoint {ω | Y ω = a} {ω | Y ω = b} := by
    rw [Set.disjoint_left]; intro ω h1 h2; exact hab (h1.symm.trans h2)
  have hU : P.real ({ω | Y ω = a} ∪ {ω | Y ω = b}) = 1 := by
    rw [measureReal_union hdisj hB, h]
  have hU' : P ({ω | Y ω = a} ∪ {ω | Y ω = b}) = 1 := by
    rw [measureReal_def] at hU
    exact (ENNReal.toReal_eq_one_iff _).1 hU
  rw [ae_iff]
  have hc : {ω | ¬(Y ω = a ∨ Y ω = b)} = ({ω | Y ω = a} ∪ {ω | Y ω = b})ᶜ := by
    ext; simp
  rw [hc, prob_compl_eq_zero_iff (hA.union hB)]
  exact hU'

lemma hdpc_integral_pair {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (a b : ℝ) (hab : a ≠ b)
    (h : P.real {ω | Y ω = a} + P.real {ω | Y ω = b} = 1) (g : ℝ → ℝ) :
    ∫ ω, g (Y ω) ∂P = g a * P.real {ω | Y ω = a} + g b * P.real {ω | Y ω = b} := by
  have hA : MeasurableSet {ω | Y ω = a} := hY (measurableSet_singleton a)
  have hB : MeasurableSet {ω | Y ω = b} := hY (measurableSet_singleton b)
  have hae := hdpc_ae_mem_pair P Y hY a b hab h
  have heq : (fun ω => g (Y ω)) =ᵐ[P] fun ω =>
      ({ω | Y ω = a}.indicator (fun _ => g a) ω + {ω | Y ω = b}.indicator (fun _ => g b) ω) := by
    filter_upwards [hae] with ω hω
    rcases hω with h1 | h1
    · simp [Set.indicator, h1, hab]
    · simp [Set.indicator, h1, hab.symm]
  rw [integral_congr_ae heq, integral_add ((integrable_const _).indicator hA)
    ((integrable_const _).indicator hB), integral_indicator_const _ hA,
    integral_indicator_const _ hB]
  simp [smul_eq_mul, mul_comm]

lemma hdpc_rad_subG {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y)
    (h : P.real {ω | Y ω = 1} = 1 / 2 ∧ P.real {ω | Y ω = -1} = 1 / 2) :
    HasSubgaussianMGF Y 1 P := by
  have hsum : P.real {ω | Y ω = 1} + P.real {ω | Y ω = -1} = 1 := by rw [h.1, h.2]; norm_num
  have hae := hdpc_ae_mem_pair P Y hY 1 (-1) (by norm_num) hsum
  have hIcc : ∀ᵐ ω ∂P, Y ω ∈ Set.Icc (-1 : ℝ) 1 := by
    filter_upwards [hae] with ω hω
    rcases hω with h1 | h1 <;> simp [h1]
  have hmean : P[Y] = 0 := by
    have := hdpc_integral_pair P Y hY 1 (-1) (by norm_num) hsum (fun x => x)
    rw [this, h.1, h.2]; norm_num
  have key := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hY.aemeasurable hIcc hmean
  have hc : (‖(1 : ℝ) - -1‖₊ / 2) ^ 2 = 1 := by
    ext
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, NNReal.coe_one]
    norm_num
  rw [hc] at key
  exact key

open MeasureTheory ProbabilityTheory Real in
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (X : Fin N → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_rad : ∀ i, P.real {ω | X i ω = 1} = 1 / 2 ∧ P.real {ω | X i ω = -1} = 1 / 2)
    (a : Fin N → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t ≤ ∑ i, a i * X i ω} ≤ Real.exp (-(t ^ 2 / (2 * ∑ i, (a i) ^ 2))) := by
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      HasSubgaussianMGF (fun ω => a i * X i ω) (a i ^ 2).toNNReal P := by
    intro i _
    have h1 := (hdpc_rad_subG P (X i) (hX_meas i) (hX_rad i)).const_mul (a i)
    convert h1 using 1
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (sq_nonneg (a i))]
    exact (mul_one (a i ^ 2)).symm
  have hind : iIndepFun (fun i ω => a i * X i ω) P :=
    hX_indep.comp (fun i x => a i * x) (fun i => measurable_const.mul measurable_id)
  have key := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub ht
  refine key.trans (le_of_eq ?_)
  congr 1
  rw [neg_div]
  congr 3
  rw [NNReal.coe_sum]
  exact Finset.sum_congr rfl (fun i _ => Real.coe_toNNReal _ (sq_nonneg _))
