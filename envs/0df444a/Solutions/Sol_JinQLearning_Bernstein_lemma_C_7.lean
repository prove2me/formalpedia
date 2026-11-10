-- Prove2me | solution 1 for JinQLearning.Bernstein.lemma_C_7
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T11:18:22.058816+00:00
-- url     : https://prove2.me/submissions/bcf32465-8604-48f9-8121-4fb30e2bc9c3

import Definitions.Def_JinQLearning_Bernstein_Statistics

open scoped BigOperators
open JinQLearning.Bernstein

def baseMDP1 : MDPComplexity.CircuitValue.MDP (Fin 1) where
  D _ := Fin 1
  c _ _ _ := 0
  p _ _ _ _ := 1
  p_nonneg _ _ _ _ := zero_le_one
  p_sum_one _ _ _ := by simp

def model1 : Model 1 1 1 where
  base := baseMDP1
  actions _ := Equiv.refl (Fin 1)
  reward_bounds _ _ _ := by simp [baseMDP1]

def path1 : Path 1 1 1 1 := fun _ => (fun _ _ => 0, fun _ => 0)

private lemma greedy_path1 (ℓ : ℝ) : GreedyPath model1 1 1 ℓ path1 := by
  intro k h x a
  rw [Subsingleton.elim a ((path1 k).1 h x)]

private lemma coarse_path1 (ℓ : ℝ) : CoarseBound model1 1 1 ℓ path1 := by
  intro k h x a hk
  fin_cases k
  simp [count, snapshot, pastEpisodes, replay, initialTables] at hk

private lemma actionMax_const_one : actionMax (fun _ : Fin 1 => (1 : ℝ)) = 1 := by
  unfold actionMax
  apply le_antisymm
  · refine Finset.sup'_le _ _ ?_
    intro _ _
    exact le_rfl
  · exact Finset.le_sup' (f := fun _ : Fin 1 => (1 : ℝ)) (Finset.mem_univ 0)

private lemma actionMax_const_zero : actionMax (fun _ : Fin 1 => (0 : ℝ)) = 0 := by
  unfold actionMax
  apply le_antisymm
  · refine Finset.sup'_le _ _ ?_
    intro _ _
    exact le_rfl
  · exact Finset.le_sup' (f := fun _ : Fin 1 => (0 : ℝ)) (Finset.mem_univ 0)

private lemma phi_path1 (ℓ : ℝ) : phi model1 1 1 ℓ path1 0 0 = 1 := by
  unfold phi
  have htab : tableValue (snapshot model1 1 1 ℓ path1 (0 : Fin 1).val) (0 : Fin 1).val
      ((path1 0).2 (0 : Fin 1).castSucc) = 1 := by
    unfold tableValue snapshot pastEpisodes replay initialTables
    simp [actionMax_const_one]
  have hopt : optimalValue model1 (0 : Fin 1).val ((path1 0).2 (0 : Fin 1).castSucc) = 0 := by
    unfold optimalValue
    rw [optimalValueAux.eq_def]
    simp [model1, baseMDP1, reward, expectation, transition, optimalValueAux, actionMax_const_zero]
  rw [htab, hopt, sub_zero]

theorem solution : ¬ (∀ c₂ : ℝ, 0 < c₂ → ∃ C : ℝ, 0 < C ∧ ∀ c₁ : ℝ, 0 < c₁ →
    ∀ (S A H K : ℕ) [NeZero S] [NeZero A] [NeZero H] [NeZero K],
    ∀ (M : Model S A H) (p : ℝ), 0 < p → p < 1 →
    ∀ (ω : Path S A H K),
    GreedyPath M c₁ c₂ (iota S A H K p) ω →
    CoarseBound M c₁ c₂ (iota S A H K p) ω →
    ∀ (h : Fin H) (w : Fin K → ℝ), (∀ k, 0 ≤ w k) →
      ∑ k, w k * phi M c₁ c₂ (iota S A H K p) ω k h ≤
        C * ((S : ℝ) * A * (Finset.univ.sup' Finset.univ_nonempty w) *
          Real.sqrt ((H : ℝ) ^ 5 * iota S A H K p) +
          Real.sqrt ((S : ℝ) * A * (∑ k, w k) *
            (Finset.univ.sup' Finset.univ_nonempty w) * (H : ℝ) ^ 5 * iota S A H K p))) := by
  intro h
  rcases h 1 zero_lt_one with ⟨C, hC, hbound⟩
  let δ : ℝ := 1 / (4 * C + 2)
  have hδ_pos : 0 < δ := by positivity
  let ε : ℝ := δ ^ 2
  have hε_pos : 0 < ε := by positivity
  let p : ℝ := Real.exp (-ε)
  have hp_pos : 0 < p := Real.exp_pos (-ε)
  have hp_lt_one : p < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hε_pos)
  have h_ineq := hbound 1 zero_lt_one 1 1 1 1 model1 p hp_pos hp_lt_one path1
    (greedy_path1 (iota 1 1 1 1 p)) (coarse_path1 (iota 1 1 1 1 p)) 0 (fun _ => 1)
    (fun _ => zero_le_one)
  have hiota : iota 1 1 1 1 p = δ ^ 2 := by
    unfold iota p ε
    simp [Real.exp_neg]
  have hsup : Finset.univ.sup' Finset.univ_nonempty (fun _ : Fin 1 => (1 : ℝ)) = 1 :=
    actionMax_const_one
  have hsum : (∑ _k : Fin 1, (1 : ℝ)) = 1 := by simp
  have h_lhs : (∑ k : Fin 1, (1 : ℝ) * phi model1 1 1 (iota 1 1 1 1 p) path1 k 0) = 1 := by
    rw [Fin.sum_univ_one, one_mul, phi_path1]
  rw [h_lhs, hiota, hsup, hsum] at h_ineq
  simp only [Nat.cast_one, one_mul, one_pow] at h_ineq
  have hsqrt : Real.sqrt (δ ^ 2) = δ := Real.sqrt_sq (le_of_lt hδ_pos)
  rw [hsqrt] at h_ineq
  have h_rhs : C * (δ + δ) < 1 := by
    have h_eq : C * (δ + δ) = (2 * C) / (4 * C + 2) := by
      dsimp [δ]
      ring
    rw [h_eq, div_lt_iff₀ (by linarith)]
    linarith
  linarith
