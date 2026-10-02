-- Prove2me | solution 1 for IntroBandits.bic_arm_two_suffices
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T15:32:54.040127+00:00
-- url     : https://prove2.me/submissions/fcece162-113f-41eb-9327-292d205654d6

import Mathlib
import Definitions.Def_IntroBandits_Agents

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm in
lemma IntroBandits.bic23624_fst_sum {Ω : Type} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (Q : Measure ((Fin 2 → ℝ) × Ω)) [IsProbabilityMeasure Q]
    (μ : Fin 2 → ℝ) :
    ∑ S, (Q {(μ, S)}).toReal = (Q.fst {μ}).toReal := by
  rw [Measure.fst_apply (measurableSet_singleton μ)]
  have hset : (Prod.fst ⁻¹' ({μ} : Set (Fin 2 → ℝ)) : Set ((Fin 2 → ℝ) × Ω))
      = ⋃ S ∈ (Finset.univ : Finset Ω), ({(μ, S)} : Set ((Fin 2 → ℝ) × Ω)) := by
    ext ⟨x, y⟩; simp [eq_comm]
  rw [hset, measure_biUnion_finset]
  · rw [ENNReal.toReal_sum]
    intro S _; exact measure_ne_top _ _
  · intro a _ b _ hab
    simp only [Function.onFun, Set.disjoint_singleton]
    intro h; apply hab; exact (Prod.ext_iff.mp h).2
  · intro b _; exact measurableSet_singleton _

open MeasureTheory ProbabilityTheory BanditAlgorithm in
lemma IntroBandits.bic23624_le {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (Q : Measure ((Fin 2 → ℝ) × Ω)) [IsProbabilityMeasure Q]
    (μ : Fin 2 → ℝ) (S : Ω) :
    (Q {(μ, S)}).toReal ≤ (IntroBandits.sigProb Q S).toReal := by
  unfold IntroBandits.sigProb
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro p hp; simp at hp; subst hp; simp

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem solution {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (Q : Measure ((Fin 2 → ℝ) × Ω)) [IsProbabilityMeasure Q]
    (F : Finset (Fin 2 → ℝ)) (hF : Q ((↑F)ᶜ ×ˢ Set.univ) = 0)
    (hprior : priorMean Q.fst F 1 ≤ priorMean Q.fst F 0)
    (rule : Ω → Fin 2 → ℝ) (hrule : ∀ S, rule S ∈ stdSimplex ℝ (Fin 2))
    (h2 : 0 < ∑ S, (sigProb Q S).toReal * rule S 1 →
      0 ≤ ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ 1 - μ 0) * rule S 1) :
    IsSingleRoundBIC Q F rule := by
  have hnn : ∀ S a, 0 ≤ rule S a := fun S a => (hrule S).1 a
  have hsum : ∀ S, rule S 0 = 1 - rule S 1 := by
    intro S; have := (hrule S).2; rw [Fin.sum_univ_two] at this; linarith
  -- B ≥ 0
  have hB : 0 ≤ ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ 1 - μ 0) * rule S 1 := by
    by_cases hpos : 0 < ∑ S, (IntroBandits.sigProb Q S).toReal * rule S 1
    · exact h2 hpos
    · have hz : ∑ S, (IntroBandits.sigProb Q S).toReal * rule S 1 = 0 :=
        le_antisymm (not_lt.mp hpos)
          (Finset.sum_nonneg fun S _ => mul_nonneg ENNReal.toReal_nonneg (hnn S 1))
      have hz' := (Finset.sum_eq_zero_iff_of_nonneg
        (fun S _ => mul_nonneg ENNReal.toReal_nonneg (hnn S 1))).mp hz
      apply le_of_eq; symm
      apply Finset.sum_eq_zero; intro μ _
      apply Finset.sum_eq_zero; intro S _
      rcases mul_eq_zero.mp (hz' S (Finset.mem_univ _)) with h | h
      · have h1 := IntroBandits.bic23624_le Q μ S
        have h0 : (Q {(μ, S)}).toReal = 0 :=
          le_antisymm (h ▸ h1) ENNReal.toReal_nonneg
        rw [h0]; ring
      · rw [h]; ring
  have hA : ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ 0 - μ 1) * rule S 0
      = (IntroBandits.priorMean Q.fst F 0 - IntroBandits.priorMean Q.fst F 1)
        + ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ 1 - μ 0) * rule S 1 := by
    unfold IntroBandits.priorMean
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro μ _
    rw [← IntroBandits.bic23624_fst_sum Q μ, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro S _
    rw [hsum S]; ring
  intro a a' haa' _
  fin_cases a <;> fin_cases a'
  · exact absurd rfl haa'
  · simp only [Fin.zero_eta, Fin.mk_one]
    rw [hA]; linarith
  · simp only [Fin.zero_eta, Fin.mk_one]
    exact hB
  · exact absurd rfl haa'
