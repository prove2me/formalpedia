-- Prove2me | solution 1 for IncentiveAwarePricing.CORP.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T04:18:29.654159+00:00
-- url     : https://prove2.me/submissions/1d4bd245-7a82-4398-a8c0-2a8fd1c3f0f9

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_IncentiveAwarePricing_CORP_Model

open MeasureTheory
open scoped RealInnerProductSpace ENNReal
open IncentiveAwarePricing.CORP

theorem solution (N : ℕ) (hN : 2 ≤ N) (v b r : Fin N → ℝ) :
    (max ((⨆ p : {p : Fin N × Fin N // p.1 ≠ p.2}, min (v p.1.1) (v p.1.2)) -
        (⨆ p : {p : Fin N × Fin N // p.1 ≠ p.2}, min (b p.1.1) (b p.1.2))) 0 ≤
      ⨆ i : Fin N, max (v i - b i) 0 * (1 - lazyAlloc b r i)) ∧
    ∀ i : Fin N, lazyAlloc b r i = 0 → (∃ j, j ≠ i ∧ lazyAlloc b r j = 1) →
      max ((⨆ j : {j : Fin N // j ≠ i}, b j) - (⨆ j : {j : Fin N // j ≠ i}, v j)) 0 ≤
        ⨆ j : {j : Fin N // j ≠ i}, max (b j - v j) 0 * lazyAlloc b r j := by
  classical
  -- basic facts on the allocation
  have hq01 : ∀ k, lazyAlloc b r k = 0 ∨ lazyAlloc b r k = 1 := by
    intro k; unfold lazyAlloc; split_ifs <;> simp
  have hwin : ∀ k, lazyAlloc b r k = 1 → ∀ j, b j ≤ b k := by
    intro k hk j
    unfold lazyAlloc at hk
    split_ifs at hk with h
    · exact h.1.1 j
    · norm_num at hk
  have huniq : ∀ k l, k ≠ l → lazyAlloc b r k = 1 → lazyAlloc b r l = 1 → False := by
    intro k l hkl hk hl
    unfold lazyAlloc at hk hl
    split_ifs at hk hl with h1 h2
    · rcases lt_or_gt_of_ne hkl with h | h
      · have := h2.1.2 k h; have := h1.1.1 l; linarith
      · have := h1.1.2 l h; have := h2.1.1 k; linarith
    all_goals simp at hk hl
  refine ⟨?_, ?_⟩
  · set R := ⨆ i : Fin N, max (v i - b i) 0 * (1 - lazyAlloc b r i) with hR
    have hRb : BddAbove (Set.range fun i : Fin N => max (v i - b i) 0 * (1 - lazyAlloc b r i)) :=
      (Set.finite_range _).bddAbove
    have hterm : ∀ k, lazyAlloc b r k = 0 → v k - b k ≤ R := by
      intro k hk
      have := le_ciSup hRb k
      simp only [hk, sub_zero, mul_one] at this
      exact (le_max_left _ _).trans this
    have hR0 : 0 ≤ R := by
      have := le_ciSup hRb ⟨0, by omega⟩
      refine le_trans ?_ this
      apply mul_nonneg (le_max_right _ _)
      rcases hq01 ⟨0, by omega⟩ with h | h <;> rw [h] <;> norm_num
    apply max_le _ hR0
    have : Nonempty {p : Fin N × Fin N // p.1 ≠ p.2} :=
      ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.ext_iff]⟩⟩
    obtain ⟨p, hp⟩ := exists_eq_ciSup_of_finite
      (f := fun p : {p : Fin N × Fin N // p.1 ≠ p.2} => min (v p.1.1) (v p.1.2))
    rw [← hp]
    have hBb : BddAbove (Set.range fun p : {p : Fin N × Fin N // p.1 ≠ p.2} =>
        min (b p.1.1) (b p.1.2)) := (Set.finite_range _).bddAbove
    have hB := le_ciSup hBb p
    obtain ⟨⟨a, c⟩, hac⟩ := p
    simp only at hB hac ⊢
    have hva := min_le_left (v a) (v c)
    have hvc := min_le_right (v a) (v c)
    by_cases h1 : lazyAlloc b r c = 0 ∧ b c ≤ b a
    · have := hterm c h1.1
      rw [min_eq_right h1.2] at hB
      linarith
    by_cases h2 : lazyAlloc b r a = 0 ∧ b a ≤ b c
    · have := hterm a h2.1
      rw [min_eq_left h2.2] at hB
      linarith
    exfalso
    rcases hq01 a with ha | ha <;> rcases hq01 c with hc | hc
    · rcases le_total (b c) (b a) with h | h
      · exact h1 ⟨hc, h⟩
      · exact h2 ⟨ha, h⟩
    · exact h2 ⟨ha, hwin c hc a⟩
    · exact h1 ⟨hc, hwin a ha c⟩
    · exact huniq a c hac ha hc
  · intro i hi ⟨j0, hj0, hq⟩
    have hne : Nonempty {j : Fin N // j ≠ i} := ⟨⟨j0, hj0⟩⟩
    have hb : (⨆ j : {j : Fin N // j ≠ i}, b j) ≤ b j0 :=
      ciSup_le fun j => hwin j0 hq j
    have hv : v j0 ≤ ⨆ j : {j : Fin N // j ≠ i}, v j :=
      le_ciSup (f := fun j : {j : Fin N // j ≠ i} => v j) (Set.finite_range _).bddAbove ⟨j0, hj0⟩
    have hR := le_ciSup (f := fun j : {j : Fin N // j ≠ i} => max (b j - v j) 0 * lazyAlloc b r j)
      (Set.finite_range _).bddAbove ⟨j0, hj0⟩
    simp only [hq, mul_one] at hR
    refine le_trans ?_ hR
    apply max_le_max _ le_rfl
    linarith
