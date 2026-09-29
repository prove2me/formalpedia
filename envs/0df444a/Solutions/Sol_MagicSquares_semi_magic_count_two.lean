-- Prove2me | solution 1 for MagicSquares.semi_magic_count_two
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-18T15:38:12.288043+00:00
-- url     : https://prove2.me/submissions/294f3d8d-5290-479d-b33d-d4a1848798c4

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresPandiagonal

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

private lemma two_structure (t : ℕ) (M : Square 2 ℕ) (hM : IsSemiMagic M t) :
    M 0 1 = t - M 0 0 ∧ M 1 0 = t - M 0 0 ∧ M 1 1 = M 0 0 := by
  have hR0 : M 0 0 + M 0 1 = t := by simpa [rowSum] using hM.1 (0 : Fin 2)
  have hR1 : M 1 0 + M 1 1 = t := by simpa [rowSum] using hM.1 (1 : Fin 2)
  have hC0 : M 0 0 + M 1 0 = t := by simpa [colSum] using hM.2 (0 : Fin 2)
  have hC1 : M 0 1 + M 1 1 = t := by simpa [colSum] using hM.2 (1 : Fin 2)
  omega

/-- Solution for `MagicSquares.semi_magic_count_two`: `H_2(t) = t + 1` (BCCG 2003, §2). A `2 x 2` semi-magic square of line sum `t` reads `[[a, t-a], [t-a, a]]` with `0 <= a <= t`, so the count is the number of admissible top-left corners. -/
theorem solution (t : ℕ) : semiMagicCount 2 t = t + 1 := by
  classical
  rw [semiMagicCount, semiMagicSquares]
  have hbij : (Finset.univ.filter (fun M : Square 2 (Fin (t + 1)) =>
        IsSemiMagic (fun i j => (M i j : ℕ)) t)).card = (Finset.range (t + 1)).card := by
    refine Finset.card_bij (fun M _ => (M 0 0 : ℕ)) ?_ ?_ ?_
    · intro M _hM
      simp only [Finset.mem_range]
      exact (M 0 0).isLt
    · intro M₁ hM₁ M₂ hM₂ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM₁ hM₂
      obtain ⟨h₁a, h₁b, h₁c⟩ := two_structure t (fun i j => (M₁ i j : ℕ)) hM₁
      obtain ⟨h₂a, h₂b, h₂c⟩ := two_structure t (fun i j => (M₂ i j : ℕ)) hM₂
      have e00 : (M₁ 0 0 : ℕ) = (M₂ 0 0 : ℕ) := heq
      have e01 : (M₁ 0 1 : ℕ) = (M₂ 0 1 : ℕ) := by omega
      have e10 : (M₁ 1 0 : ℕ) = (M₂ 1 0 : ℕ) := by omega
      have e11 : (M₁ 1 1 : ℕ) = (M₂ 1 1 : ℕ) := by omega
      have hall : ∀ i j : Fin 2, (M₁ i j : ℕ) = (M₂ i j : ℕ) := by
        intro i j
        fin_cases i <;> fin_cases j
        · exact e00
        · exact e01
        · exact e10
        · exact e11
      funext i j
      exact Fin.ext (hall i j)
    · intro a ha
      simp only [Finset.mem_range] at ha
      let M : Square 2 (Fin (t + 1)) :=
        ![![⟨a, by omega⟩, ⟨t - a, by omega⟩], ![⟨t - a, by omega⟩, ⟨a, by omega⟩]]
      refine ⟨M, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨fun i => ?_, fun j => ?_⟩
        · fin_cases i <;> simp [rowSum, Fin.sum_univ_two, M] <;> omega
        · fin_cases j <;> simp [colSum, Fin.sum_univ_two, M] <;> omega
      · simp [M]
  rw [hbij, Finset.card_range]
