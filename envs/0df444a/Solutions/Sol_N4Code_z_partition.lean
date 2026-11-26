-- Prove2me | solution 1 for N4Code.z_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:20:08.856423+00:00
-- url     : https://prove2.me/submissions/edb8ebc8-49ee-487a-ba50-98e8162ce37f

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C _C' : Code n) (t₁ t₂ : Fin n) :
    ∀ y : Word n, ∃! i : Fin 5, ZSet C t₁ t₂ i y := by
  intro y
  by_cases heq : y t₁ = y t₂
  · refine ⟨⟨0, by decide⟩, ?_, ?_⟩
    · simp [ZSet, Z1, heq]
    · intro j hj
      have hz := by simpa [ZSet] using hj
      fin_cases j
      · rfl
      · exfalso
        exact hz.1 heq
      · exfalso
        exact hz.1 heq
      · exfalso
        exact hz.1 heq
      · exfalso
        exact hz.1 heq
  · have hne : y t₁ ≠ y t₂ := heq
    by_cases h2 : dO C y ≤ min (dP C y) (dPp2 C t₁ t₂ y)
    · refine ⟨⟨1, by decide⟩, ?_, ?_⟩
      · simp [ZSet, Z2, hne, h2]
      · intro j hj
        have hz := by simpa [ZSet] using hj
        fin_cases j
        · exfalso
          exact hne hz
        · rfl
        · exfalso
          exact (not_lt_of_ge h2) hz.2.1
        · exfalso
          exact (not_lt_of_ge h2) hz.2.1
        · exfalso
          exact (not_lt_of_ge h2) hz.2.1
    · have hgt : dO C y > min (dP C y) (dPp2 C t₁ t₂ y) := lt_of_not_ge h2
      by_cases h3 : dP C y ≤ min (dO C y) (dOp2 C t₁ t₂ y)
      · refine ⟨⟨2, by decide⟩, ?_, ?_⟩
        · simp [ZSet, Z3, hne, hgt, h3]
        · intro j hj
          have hz := by simpa [ZSet] using hj
          fin_cases j
          · exfalso
            exact hne hz
          · exfalso
            exact (not_lt_of_ge hz.2) hgt
          · rfl
          · exfalso
            exact (not_lt_of_ge h3) hz.2.2.1
          · exfalso
            exact (not_lt_of_ge h3) hz.2.2.1
      · have hgt2 : dP C y > min (dO C y) (dOp2 C t₁ t₂ y) := lt_of_not_ge h3
        by_cases h4 : min (dO C y) (dOp2 C t₁ t₂ y) ≤ dPp2 C t₁ t₂ y
        · refine ⟨⟨4, by decide⟩, ?_, ?_⟩
          · simp [ZSet, Z5, hne, hgt, hgt2, h4]
          · intro j hj
            have hz := by simpa [ZSet] using hj
            fin_cases j
            · exfalso
              exact hne hz
            · exfalso
              exact (not_lt_of_ge hz.2) hgt
            · exfalso
              exact h3 hz.2.2
            · exfalso
              exact (not_lt_of_ge h4) hz.2.2.2
            · rfl
        · refine ⟨⟨3, by decide⟩, ?_, ?_⟩
          · refine ⟨hne, hgt, hgt2, ?_⟩
            exact lt_of_not_ge h4
          · intro j hj
            have hz := by simpa [ZSet] using hj
            fin_cases j
            · exfalso
              exact hne hz
            · exfalso
              exact (not_lt_of_ge hz.2) hgt
            · exfalso
              exact h3 hz.2.2
            · rfl
            · exfalso
              exact h4 hz.2.2.2
end N4Code
