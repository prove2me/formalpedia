-- Prove2me | solution 1 for GoTBandit.Main.lemma_IV_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:10:25.227883+00:00
-- url     : https://prove2.me/submissions/76a9c344-a460-464f-a9df-37185d38aa98

import Mathlib
import Definitions.Def_GoTBandit_Main_Assignment

open Finset GoTBandit.Main

theorem solution {N M : ℕ} (hNM : N ≤ M) (μ μhat : Fin N → Fin M → ℝ)
    (hμ : ∀ n i, 0 < μ n i) (Δ : ℝ) (hest : ∀ n i, |μhat n i - μ n i| < Δ)
    (hΔ : Δ ≤ (J1 μ - J2 μ) / (2 * N)) :
    {a | IsOptimal μhat a} ⊆ {a | IsOptimal μ a} := by
  intro a ha
  simp only [Set.mem_ofPred_eq] at ha ⊢
  intro a'
  by_contra hlt
  push Not at hlt
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : a' = a := Subsingleton.elim _ _
    subst this; exact lt_irrefl _ hlt
  -- the maximizer of the true objective
  haveI : Nonempty (Fin N → Fin M) := ⟨a⟩
  obtain ⟨aS, haS⟩ := Finite.exists_max (obj μ)
  have hJ1 : J1 μ = obj μ aS :=
    le_antisymm (ciSup_le haS) (le_ciSup (Finite.bddAbove_range _) aS)
  have hlt' : obj μ a < J1 μ := lt_of_lt_of_le hlt (hJ1 ▸ haS a')
  have hJ2 : obj μ a ≤ J2 μ := by
    unfold J2
    apply le_csSup
    · exact ⟨J1 μ, fun x hx => le_of_lt hx.2⟩
    · exact ⟨⟨a, rfl⟩, hlt'⟩
  -- estimation error of the objective
  have herr : ∀ b : Fin N → Fin M, |obj μhat b - obj μ b| < N * Δ := by
    intro b
    have hne : (univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, mem_univ _⟩
    have h1 : obj μhat b - obj μ b = ∑ n, (μhat n (b n) - μ n (b n)) * noColl b (b n) := by
      simp only [obj, gUtil, ← Finset.sum_sub_distrib, sub_mul]
    rw [h1]
    calc |∑ n, (μhat n (b n) - μ n (b n)) * noColl b (b n)|
        ≤ ∑ n, |(μhat n (b n) - μ n (b n)) * noColl b (b n)| := Finset.abs_sum_le_sum_abs _ _
      _ < ∑ _n : Fin N, Δ := by
          apply Finset.sum_lt_sum_of_nonempty hne
          intro n _
          have hnc : |noColl b (b n)| ≤ 1 := by
            unfold noColl; split_ifs <;> simp
          rw [abs_mul]
          calc |μhat n (b n) - μ n (b n)| * |noColl b (b n)|
              ≤ |μhat n (b n) - μ n (b n)| * 1 :=
                mul_le_mul_of_nonneg_left hnc (abs_nonneg _)
            _ < Δ := by rw [mul_one]; exact hest n (b n)
      _ = N * Δ := by simp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h2 : 2 * N * Δ ≤ J1 μ - J2 μ := by
    rw [le_div_iff₀ (by positivity)] at hΔ; linarith
  have e1 := herr a
  have e2 := herr aS
  rw [abs_lt] at e1 e2
  have := ha aS
  linarith
