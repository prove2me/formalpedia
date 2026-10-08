-- Prove2me | solution 1 for Gomory69.SpecialGroups.lemma_p505
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:17:09.57387+00:00
-- url     : https://prove2.me/submissions/133093ee-d658-41bd-89a8-6ef12f0f8f5e

import Mathlib

theorem solution (p : ℤ) (hp : p = 2 ∨ p = 3) (t s : ℤ)
    (ht₀ : 0 < t) (htp : t < p) (hs₀ : 0 ≤ s) (hsp : s < p) :
    ∃ t' t'' : ℤ, 0 ≤ t' ∧ t' ≤ t ∧ 0 ≤ t'' ∧ t'' ≤ t ∧ t' + s ≡ t'' [ZMOD p] := by
  rcases hp with rfl | rfl
  · interval_cases t
    interval_cases s
    · exact ⟨0, 0, by norm_num [Int.ModEq]⟩
    · exact ⟨0, 1, by norm_num [Int.ModEq]⟩
  · interval_cases t <;> interval_cases s
    · exact ⟨0, 0, by norm_num [Int.ModEq]⟩
    · exact ⟨0, 1, by norm_num [Int.ModEq]⟩
    · exact ⟨1, 0, by norm_num [Int.ModEq]⟩
    · exact ⟨0, 0, by norm_num [Int.ModEq]⟩
    · exact ⟨0, 1, by norm_num [Int.ModEq]⟩
    · exact ⟨0, 2, by norm_num [Int.ModEq]⟩

#print axioms solution
