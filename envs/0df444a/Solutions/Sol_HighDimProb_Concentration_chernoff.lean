-- Prove2me | solution 1 for HighDimProb.Concentration.chernoff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T21:44:05.856723+00:00
-- url     : https://prove2.me/submissions/efe925ce-7ba9-4388-b2d2-4277a5f00c24

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

lemma hdpc_ber {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (p : ℝ)
    (h : P.real {ω | Y ω = 1} = p ∧ P.real {ω | Y ω = 0} = 1 - p) :
    (∀ᵐ ω ∂P, Y ω ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ l : ℝ, mgf Y P l = 1 + p * (exp l - 1)) ∧
      ∫ ω, Y ω ∂P = p ∧ 0 ≤ p := by
  have hsum : P.real {ω | Y ω = 1} + P.real {ω | Y ω = 0} = 1 := by rw [h.1, h.2]; ring
  have hae := hdpc_ae_mem_pair P Y hY 1 0 one_ne_zero hsum
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hae] with ω hω
    rcases hω with h1 | h1 <;> simp [h1]
  · intro l
    have h2 := hdpc_integral_pair P Y hY 1 0 one_ne_zero hsum (fun x => exp (l * x))
    rw [mgf, h2, h.1, h.2]
    simp only [mul_one, mul_zero, exp_zero]
    ring
  · have h2 := hdpc_integral_pair P Y hY 1 0 one_ne_zero hsum (fun x => x)
    rw [h2, h.1, h.2]; ring
  · rw [← h.1]; exact measureReal_nonneg

open MeasureTheory ProbabilityTheory Real in
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (X : Fin N → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P) (p : Fin N → ℝ)
    (hX_ber : ∀ i, P.real {ω | X i ω = 1} = p i ∧ P.real {ω | X i ω = 0} = 1 - p i)
    {t : ℝ} (ht : (∫ ω, ∑ i, X i ω ∂P) < t) :
    P.real {ω | t ≤ ∑ i, X i ω} ≤
      Real.exp (-(∫ ω, ∑ i, X i ω ∂P)) *
        (Real.exp 1 * (∫ ω, ∑ i, X i ω ∂P) / t) ^ t := by
  have hB := fun i => hdpc_ber P (X i) (hX_meas i) (p i) (hX_ber i)
  have hμ : ∫ ω, ∑ i, X i ω ∂P = ∑ i, p i := by
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl (fun i _ => (hB i).2.2.1)
    · intro i _
      exact Integrable.of_mem_Icc 0 1 (hX_meas i).aemeasurable (hB i).1
  have hμ0 : 0 ≤ ∑ i, p i := Finset.sum_nonneg (fun i _ => (hB i).2.2.2)
  rw [hμ] at ht ⊢
  set μ := ∑ i, p i with hμdef
  have key : ∀ l : ℝ, 0 ≤ l →
      P.real {ω | t ≤ ∑ i, X i ω} ≤ exp (-l * t) * exp (μ * (exp l - 1)) := by
    intro l hl
    have hint : Integrable (fun ω => exp (l * (∑ i, X i) ω)) P :=
      hX_indep.integrable_exp_mul_sum hX_meas
        (fun i _ => integrable_exp_mul_of_mem_Icc (hX_meas i).aemeasurable (hB i).1)
    have h1 := measure_ge_le_exp_mul_mgf (X := ∑ i, X i) t hl hint
    have hset : {ω | t ≤ ∑ i, X i ω} = {ω | t ≤ (∑ i, X i) ω} := by
      ext ω; simp [Finset.sum_apply]
    rw [hset]
    refine h1.trans ?_
    gcongr
    rw [hX_indep.mgf_sum hX_meas, hμdef, Finset.sum_mul, Real.exp_sum]
    apply Finset.prod_le_prod (fun i _ => mgf_nonneg)
    intro i _
    rw [(hB i).2.1 l]
    linarith [Real.add_one_le_exp (p i * (exp l - 1))]
  rcases hμ0.lt_or_eq with hpos | hzero
  · have htpos : 0 < t := hpos.trans ht
    have hr : 0 < t / μ := div_pos htpos hpos
    have hl : 0 ≤ log (t / μ) := log_nonneg ((one_le_div hpos).2 ht.le)
    have hμne : μ ≠ 0 := hpos.ne'
    have hemu : 0 < exp 1 * μ := mul_pos (exp_pos 1) hpos
    refine (key _ hl).trans (le_of_eq ?_)
    rw [exp_log hr, rpow_def_of_pos (div_pos hemu htpos), ← exp_add, ← exp_add]
    congr 1
    rw [log_div hemu.ne' htpos.ne', log_mul (exp_pos 1).ne' hμne, log_exp,
      log_div htpos.ne' hμne]
    field_simp
    ring
  · have htpos : 0 < t := by rw [hzero]; exact ht
    have hR : exp (-μ) * (exp 1 * μ / t) ^ t = 0 := by
      rw [← hzero, mul_zero, zero_div, zero_rpow htpos.ne', mul_zero]
    rw [hR]
    by_contra hcon
    rw [not_le] at hcon
    set q := P.real {ω | t ≤ ∑ i, X i ω} with hq
    have h1 := key ((|log q| + 1) / t) (div_nonneg (by positivity) htpos.le)
    rw [← hzero, zero_mul, exp_zero, mul_one] at h1
    have h2 : -((|log q| + 1) / t) * t = -(|log q| + 1) := by
      rw [neg_mul, div_mul_cancel₀ _ htpos.ne']
    rw [h2] at h1
    have h3 : exp (-(|log q| + 1)) < q := by
      calc exp (-(|log q| + 1)) < exp (log q) := exp_lt_exp.2 (by linarith [neg_abs_le (log q)])
        _ = q := exp_log hcon
    linarith
