-- Prove2me | solution 1 for IncrKnapsack.PTAS.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T02:55:03.007605+00:00
-- url     : https://prove2.me/submissions/7a007b85-08ca-4cdb-8241-73c0af0bf70b

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model
import Theorems.Thm_IncrKnapsack_PTAS_profit_rounding
import Theorems.Thm_IncrKnapsack_PTAS_lemma_7
import Theorems.Thm_IncrKnapsack_PTAS_lemma_10
import Theorems.Thm_IncrKnapsack_PTAS_lemma_11

open Classical
open Finset BigOperators
open IncrKnapsack.PTAS

theorem solution :
    ∀ ε' : ℝ, 0 < ε' → ∃ K : ℕ, 4 < K ∧
      ∀ (I : Instance), I.Standing →
      ∀ Sstar : Sol I, IsOptimal I I.p Sstar →
      ∀ (Φ : ℕ → Finset ℝ) (A : ℕ → Subroutine I) (jt : ℕ → ℕ → ℕ) (ϕt : ℕ → ℕ → ℝ),
        (∀ ξ < K, IsProfitGrid I K ξ (Φ ξ) ∧ IsSubroutine I K ξ (A ξ) ∧
          IsTraceback I K ξ (Φ ξ) (A ξ) (jt ξ) (ϕt ξ)) →
        (∀ ξ < K, Feasible I (algOut I K ξ (Φ ξ) (A ξ) (jt ξ) (ϕt ξ))) ∧
        ∃ ξ < K, (1 - ε') * Psi I I.p Sstar ≤
          Psi I I.p (algOut I K ξ (Φ ξ) (A ξ) (jt ξ) (ϕt ξ)) := by
  intro ε' hε'
  refine ⟨⌈8 / ε'⌉₊ + 8, by omega, ?_⟩
  set K : ℕ := ⌈8 / ε'⌉₊ + 8 with hKdef
  have hK4 : 4 < K := by omega
  have hKpos : (0 : ℝ) < K := by positivity
  have hK8 : (8 : ℝ) / ε' ≤ K := by
    have := Nat.le_ceil (8 / ε')
    have : ((⌈8 / ε'⌉₊ : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : ⌈8 / ε'⌉₊ ≤ K)
    linarith
  have hK8' : (8 : ℝ) ≤ K := by exact_mod_cast (by omega : 8 ≤ K)
  have heps : eps K = 1 / (K : ℝ) := rfl
  have he8 : 8 * eps K ≤ ε' := by
    rw [heps]
    rw [div_le_iff₀ hε'] at hK8
    rw [mul_one_div, div_le_iff₀ hKpos]; linarith
  have he7 : 7 * eps K ≤ 1 := by
    rw [heps, mul_one_div, div_le_iff₀ hKpos]; linarith
  have hepos : 0 ≤ eps K := by rw [heps]; positivity
  intro I hI Sstar hSstar Φ A jt ϕt hall
  refine ⟨fun ξ hξ => lemma_10 I hI K hK4 ξ hξ (Φ ξ) (A ξ) (jt ξ) (ϕt ξ) (hall ξ hξ).2.1
    (hall ξ hξ).2.2, ?_⟩
  -- the empty solution is feasible
  have hempty : Feasible I (fun _ => none) := by
    intro t
    have : Sol.set (I := I) (fun _ => none) t = ∅ := by
      ext i; simp [Sol.set]
    rw [this, Finset.sum_empty]; exact hI.W_nonneg t
  have hPsiEmpty : ∀ q : Fin I.n → ℝ, Psi I q (fun _ => none) = 0 := by
    intro q
    unfold Psi
    have : ∀ t, Sol.set (I := I) (fun _ => none) t = ∅ := by
      intro t; ext i; simp [Sol.set]
    simp [this]
  -- an optimal solution for the rounded profits
  obtain ⟨S2, hS2mem, hS2max⟩ := Finset.exists_max_image (univ.filter (Feasible I))
    (Psi I (pr I K)) ⟨fun _ => none, by simp [hempty]⟩
  have hS2feas : Feasible I S2 := by simpa using hS2mem
  have hS2opt : IsOptimal I (pr I K) S2 :=
    ⟨hS2feas, fun S' hS' => hS2max S' (by simpa using hS')⟩
  -- a good shift, by averaging (Lemma 7)
  have h7 := lemma_7 I hI K hK4 (pr I K) S2
  obtain ⟨ξ, hξmem, hξ⟩ : ∃ ξ ∈ range K,
      (1 - eps K) * Psi I (pr I K) S2 ≤ Psi I (pr I K) (restrictGood I K ξ S2) := by
    apply Finset.exists_le_of_sum_le (by simp)
    rw [Finset.sum_const, card_range, nsmul_eq_mul]
    have : ∑ ξ ∈ range K, Psi I (pr I K) (restrictGood I K ξ S2) =
        (K : ℝ) * ((1 - eps K) * Psi I (pr I K) S2) := by
      rw [← h7]; field_simp
    rw [this]
  have hξK : ξ < K := by simpa using hξmem
  refine ⟨ξ, hξK, ?_⟩
  obtain ⟨hΦ, hA, htr⟩ := hall ξ hξK
  have h11 := lemma_11 I hI K hK4 ξ hξK S2 hS2opt hξ (Φ ξ) (A ξ) (jt ξ) (ϕt ξ) hΦ hA htr
  set Sb := algOut I K ξ (Φ ξ) (A ξ) (jt ξ) (ϕt ξ)
  have hr1 := (profit_rounding I hI K hK4 Sb).1
  have hr2 := (profit_rounding I hI K hK4 Sstar).2
  have hPsiStar : 0 ≤ Psi I I.p Sstar := by
    have := hSstar.2 _ hempty; rw [hPsiEmpty] at this; exact this
  have hpmin : 0 < pmin I := by
    unfold pmin
    have hne : (univ : Finset (Fin I.n)).Nonempty := ⟨⟨0, hI.n_pos⟩, mem_univ _⟩
    rw [dif_pos hne, Finset.lt_inf'_iff]
    intro i _; exact hI.p_pos i
  have hcmp : Psi I (pr I K) Sstar ≤ Psi I (pr I K) S2 := hS2opt.2 _ hSstar.1
  have h7nn : 0 ≤ 1 - 7 * eps K := by linarith
  -- chain
  have c1 : pmin I * ((1 - 7 * eps K) * Psi I (pr I K) Sstar) ≤ Psi I I.p Sb := by
    calc pmin I * ((1 - 7 * eps K) * Psi I (pr I K) Sstar)
        ≤ pmin I * ((1 - 7 * eps K) * Psi I (pr I K) S2) := by
          apply mul_le_mul_of_nonneg_left _ hpmin.le
          exact mul_le_mul_of_nonneg_left hcmp h7nn
      _ ≤ pmin I * Psi I (pr I K) Sb := mul_le_mul_of_nonneg_left h11 hpmin.le
      _ ≤ _ := hr1
  have c2 : (1 - 7 * eps K) * ((1 - eps K) * Psi I I.p Sstar) ≤
      (1 - 7 * eps K) * (pmin I * Psi I (pr I K) Sstar) :=
    mul_le_mul_of_nonneg_left hr2 h7nn
  have c3 : (1 - ε') * Psi I I.p Sstar ≤ (1 - 7 * eps K) * ((1 - eps K) * Psi I I.p Sstar) := by
    have : (1 - ε') ≤ (1 - 7 * eps K) * (1 - eps K) := by nlinarith
    nlinarith
  nlinarith
