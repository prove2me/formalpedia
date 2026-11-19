-- Prove2me | solution 1 for MohriFoML.OnlineToBatch.hoeffding_inequality
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:43:20.231229+00:00
-- url     : https://prove2.me/submissions/99bc915d-1128-48d6-b99e-40de3a9efd33

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ}
    (X : Fin m → Ω → ℝ) (a b : Fin m → ℝ)
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hX : ∀ i ω, X i ω ∈ Set.Icc (a i) (b i)) :
    ∀ ε : ℝ, 0 < ε →
      μ.real {ω | ε ≤ (∑ i, X i ω) - ∫ ω', (∑ i, X i ω') ∂μ}
          ≤ Real.exp (-2 * ε ^ 2 / ∑ i, (b i - a i) ^ 2) ∧
        μ.real {ω | (∑ i, X i ω) - ∫ ω', (∑ i, X i ω') ∂μ ≤ -ε}
          ≤ Real.exp (-2 * ε ^ 2 / ∑ i, (b i - a i) ^ 2) := by
  intro ε hε
  have hint : ∀ i, Integrable (X i) μ := fun i =>
    Integrable.of_mem_Icc (a i) (b i) (hmeas i).aemeasurable (Filter.Eventually.of_forall (hX i))
  have hE : ∫ ω', (∑ i, X i ω') ∂μ = ∑ i, ∫ ω, X i ω ∂μ := integral_finset_sum _ (fun i _ => hint i)
  set Y : Fin m → Ω → ℝ := fun i ω => X i ω - ∫ ω, X i ω ∂μ with hY
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      HasSubgaussianMGF (Y i) ((‖b i - a i‖₊ / 2) ^ 2) μ := fun i _ =>
    hasSubgaussianMGF_of_mem_Icc (hmeas i).aemeasurable (Filter.Eventually.of_forall (hX i))
  have hindY : iIndepFun Y μ := hindep.comp (fun i x => x - ∫ ω, X i ω ∂μ)
    (fun i => measurable_id.sub_const _)
  have hc : ∑ i, (((‖b i - a i‖₊ / 2) ^ 2 : NNReal) : ℝ) = (∑ i, (b i - a i) ^ 2) / 4 := by
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro i _
    push_cast
    rw [Real.norm_eq_abs, div_pow, sq_abs]; ring
  have hexp : -ε ^ 2 / (2 * ((∑ i, (b i - a i) ^ 2) / 4)) = -2 * ε ^ 2 / ∑ i, (b i - a i) ^ 2 := by
    rcases eq_or_ne (∑ i, (b i - a i) ^ 2) 0 with h0 | h0
    · rw [h0]; simp
    · field_simp; ring
  have hsumY : ∀ ω, ∑ i, Y i ω = (∑ i, X i ω) - ∫ ω', (∑ i, X i ω') ∂μ := by
    intro ω; rw [hE]; simp [hY, Finset.sum_sub_distrib]
  constructor
  · have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindY hsub hε.le
    simp only [NNReal.coe_sum] at hH
    rw [hc, hexp] at hH
    have hset : {ω | ε ≤ (∑ i, X i ω) - ∫ ω', (∑ i, X i ω') ∂μ} = {ω | ε ≤ ∑ i ∈ Finset.univ, Y i ω} := by
      ext ω; simp [hsumY]
    rw [hset]; exact hH
  · have hsubN : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        HasSubgaussianMGF (fun ω => -Y i ω) ((‖b i - a i‖₊ / 2) ^ 2) μ := fun i hi => (hsub i hi).neg
    have hindN : iIndepFun (fun i ω => -Y i ω) μ := hindY.comp (fun i x => -x) (fun i => measurable_neg)
    have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindN hsubN hε.le
    simp only [NNReal.coe_sum] at hH
    rw [hc, hexp] at hH
    have hset : {ω | (∑ i, X i ω) - ∫ ω', (∑ i, X i ω') ∂μ ≤ -ε} =
        {ω | ε ≤ ∑ i ∈ Finset.univ, -Y i ω} := by
      ext ω; simp only [Set.mem_ofPred_eq, Finset.sum_neg_distrib]; rw [hsumY]; constructor <;> intro h <;> linarith
    rw [hset]; exact hH
