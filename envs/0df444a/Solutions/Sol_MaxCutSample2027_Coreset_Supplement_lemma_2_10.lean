-- Prove2me | solution 1 for MaxCutSample2027.Coreset.Supplement.lemma_2_10
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-26T23:53:15.034902+00:00
-- url     : https://prove2.me/submissions/4b8a0bba-4a1f-44fe-abd5-c53495fba838

import Definitions.Def_MaxCutSample2027_Coreset_Supplement_sampling
open scoped BigOperators
noncomputable section

set_option autoImplicit false

open MaxCutSample2027
open MaxCutSample2027.Coreset
open MaxCutSample2027.Coreset.Supplement

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (hbound : ∀ u v, A u v ≤ 1) :
    H A p ^ 2 ≤ (∑ v, weightedDegree A v / p v) / (Fintype.card V : ℝ) ^ 3 ∧
    ((∀ v, weightedDegree A v / (Fintype.card V : ℝ) ^ 2 ≤ p v) → H A p ≤ 1) := by
  let N : ℝ := Fintype.card V
  have hN : 0 < N := by
    change 0 < (Fintype.card V : ℝ)
    exact_mod_cast Fintype.card_pos (α := V)
  let moment (v : V) := ∑ u, p u * (K A p u v) ^ 2
  let column (v : V) := (∑ u, A u v / p u) / N ^ 4
  have column_nonneg (v : V) : 0 ≤ column v := by
    dsimp [column]
    exact div_nonneg (Finset.sum_nonneg fun u _ => div_nonneg (hA.2.2 u v) (hp.1 u).le) (by positivity)
  have square_column (v : V) : (p v * Real.sqrt (moment v)) ^ 2 ≤ column v := by
    have nonneg : 0 ≤ moment v :=
      Finset.sum_nonneg fun u _ => mul_nonneg (hp.1 u).le (sq_nonneg _)
    rw [mul_pow, Real.sq_sqrt nonneg]
    dsimp [moment, column]
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_le_sum
    intro u _
    have heq : p v ^ 2 * (p u * K A p u v ^ 2) = (A u v ^ 2 / p u) / N ^ 4 := by
      change p v ^ 2 * (p u * (A u v / (N ^ 2 * p u * p v)) ^ 2) = _
      field_simp [hN.ne', (hp.1 u).ne', (hp.1 v).ne']
    rw [heq]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply div_le_div_of_nonneg_right _ (hp.1 u).le
    nlinarith [mul_nonneg (hA.2.2 u v) (sub_nonneg.mpr (hbound u v))]
  have bound : H A p ^ 2 ≤ (∑ v, weightedDegree A v / p v) / N ^ 3 := by
    calc
      _ = (∑ v, p v * Real.sqrt (moment v)) ^ 2 := rfl
      _ ≤ (∑ _v : V, (1 : ℝ)) * ∑ v, column v := by
        apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (by simp) (fun v _ => column_nonneg v)
        intro v _
        simpa only [one_mul] using square_column v
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, column]
        rw [← Finset.sum_div, Finset.sum_comm]
        simp_rw [← Finset.sum_div]
        change N * ((∑ u, weightedDegree A u / p u) / N ^ 4) = _
        field_simp [hN.ne']
  refine ⟨bound, ?_⟩
  intro dominates
  have hsum : (∑ v, weightedDegree A v / p v) ≤ N ^ 3 := by
    calc
      _ ≤ ∑ _v : V, N ^ 2 := by
        apply Finset.sum_le_sum
        intro v _
        apply (div_le_iff₀ (hp.1 v)).2
        rw [mul_comm]
        exact (div_le_iff₀ (by positivity : 0 < N ^ 2)).1 (dominates v)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; change N * N ^ 2 = _; ring
  have hsquare : H A p ^ 2 ≤ 1 := bound.trans (div_le_one (by positivity) |>.2 hsum)
  nlinarith
