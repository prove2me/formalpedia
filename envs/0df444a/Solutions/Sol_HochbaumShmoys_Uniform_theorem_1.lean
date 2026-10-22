-- Prove2me | solution 1 for HochbaumShmoys.Uniform.theorem_1
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:01:24.166405+00:00
-- url     : https://prove2.me/submissions/72c450c5-a823-4df4-872a-d33421edc124

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_Packing
import Definitions.Def_HochbaumShmoys_Uniform_BinarySearch
open HochbaumShmoys.Uniform

noncomputable def g69g_p : Fin 4 → ℝ := ![1, 1, 1, 1/10]
noncomputable def g69g_s : Fin 4 → ℝ := ![1, 1, 1, 2/155]
def g69g_σ : Fin 4 → Fin 4 := fun j => j
def g69g_τ : Fin 4 → Fin 4 := ![0, 1, 2, 0]

open Classical in
noncomputable def g69g_D : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Option (Fin 4 → Fin 4) :=
  fun p b => if p = g69g_p ∧ IsRelaxedFeasible (6 / 2) p b g69g_σ then some g69g_σ
    else if h : ∃ σ, IsTrulyFeasible p b σ then some h.choose else none

theorem g69g_D_ok : IsRelaxedDecisionProcedure (6 / 2) g69g_D := by
  intro p b hp hb
  constructor
  · intro σ hσ
    unfold g69g_D at hσ
    split_ifs at hσ with h1 h2
    · cases hσ; exact h1.2
    · cases hσ
      intro i
      have := h2.choose_spec i
      have := hb i
      linarith
  · intro hn σ hσ
    unfold g69g_D at hn
    split_ifs at hn with h1 h2
    exact h2 ⟨σ, hσ⟩

theorem g69g_iSup_s : (⨆ i, g69g_s i) = 1 := by
  apply le_antisymm
  · apply ciSup_le; intro i; fin_cases i <;> simp [g69g_s] <;> norm_num
  · have := le_ciSup (Finite.bddAbove_range g69g_s) 0
    simpa [g69g_s] using this

theorem g69g_sum_p : ∑ j, g69g_p j = 31 / 10 := by
  simp [g69g_p, Fin.sum_univ_four]; norm_num

theorem g69g_iter : iterationCount 4 6 = 1 := by
  unfold iterationCount
  have h : Real.logb 2 (4 : ℕ) + Real.logb 2 (3 / 6) = 1 := by
    rw [← Real.logb_mul (by norm_num) (by norm_num)]
    norm_num
  rw [h]; simp

theorem g69g_binLoad (i : Fin 4) : binLoad g69g_p g69g_σ i = g69g_p i := by
  unfold binLoad g69g_σ
  rw [Finset.filter_eq' Finset.univ i]; simp

theorem g69g_feas : IsRelaxedFeasible (6 / 2) g69g_p
    (fun i => (initialLower g69g_p g69g_s + initialUpper g69g_p g69g_s) / 2 * g69g_s i) g69g_σ := by
  intro i
  rw [g69g_binLoad]
  unfold initialLower initialUpper
  rw [g69g_iSup_s, g69g_sum_p]
  fin_cases i <;> simp [g69g_p, g69g_s] <;> norm_num

theorem g69g_output : binarySearch g69g_D g69g_p g69g_s (by norm_num) (iterationCount 4 6) = g69g_σ := by
  rw [g69g_iter]
  unfold binarySearch
  rw [Function.iterate_one]
  unfold searchStep
  have : g69g_D g69g_p (fun i => (initialLower g69g_p g69g_s + initialUpper g69g_p g69g_s) / 2 * g69g_s i)
      = some g69g_σ := by
    unfold g69g_D; rw [if_pos ⟨rfl, g69g_feas⟩]
  simp only [this]

theorem g69g_mt_σ : (155 : ℝ) / 20 ≤ makespan g69g_p g69g_s g69g_σ := by
  unfold makespan
  refine le_trans ?_ (le_ciSup (Finite.bddAbove_range _) 3)
  unfold machineTime g69g_σ
  rw [Finset.filter_eq' Finset.univ 3]; simp [g69g_p, g69g_s]; norm_num

theorem g69g_mt_τ : makespan g69g_p g69g_s g69g_τ ≤ 11 / 10 := by
  unfold makespan
  apply ciSup_le; intro i
  unfold machineTime
  rw [Finset.sum_filter, Fin.sum_univ_four]
  fin_cases i <;> simp [g69g_p, g69g_s, g69g_τ] <;> norm_num

theorem solution : ¬ (∀ (ε : ℝ) (hε : 0 < ε) (m n : ℕ) (hm : 0 < m) (s : Fin m → ℝ)
    (p : Fin n → ℝ) (hs : ∀ i, 0 < s i) (hp : ∀ j, 0 < p j)
    (D : (Fin n → ℝ) → (Fin m → ℝ) → Option (Fin n → Fin m))
    (hD : IsRelaxedDecisionProcedure (ε / 2) D) (τ : Fin n → Fin m),
    makespan p s (binarySearch D p s hm (iterationCount m ε)) ≤
      (1 + ε) * makespan p s τ) := by
  intro H
  have h := H 6 (by norm_num) 4 4 (by norm_num) g69g_s g69g_p
    (by intro i; fin_cases i <;> simp [g69g_s])
    (by intro j; fin_cases j <;> simp [g69g_p]) g69g_D g69g_D_ok g69g_τ
  rw [g69g_output] at h
  have h1 := g69g_mt_σ
  have h2 := g69g_mt_τ
  nlinarith
