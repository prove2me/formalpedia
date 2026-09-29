-- Prove2me | solution 1 for MagicSquares.symmetric_magic_count_two
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-18T15:38:15.691685+00:00
-- url     : https://prove2.me/submissions/2ab77a63-6f81-48a3-8b42-49dafd072f28

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

private theorem magic_count_two (t : ℕ) : magicCount 2 t = if 2 ∣ t then 1 else 0 := by
  classical
  rw [magicCount, magicSquares]
  by_cases h : 2 ∣ t
  · obtain ⟨e, rfl⟩ := h
    let C : Square 2 (Fin (2 * e + 1)) := fun _ _ => ⟨e, by omega⟩
    rw [if_pos (dvd_mul_right 2 e), Finset.card_eq_one]
    refine ⟨C, ?_⟩
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨fun i => ?_, fun j => ?_⟩, ?_, ?_⟩
      · fin_cases i <;> simp [rowSum, C]
      · fin_cases j <;> simp [colSum, C]
      · simp [diagSum, C]
      · simp [antiDiagSum, C]
    · intro M hM
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
      obtain ⟨hsa, hsb, hsc⟩ := two_structure (2 * e) (fun i j => (M i j : ℕ)) hM.1
      have hD : (M 0 0 : ℕ) + (M 1 1 : ℕ) = 2 * e := by
        simpa [diagSum, Fin.sum_univ_two] using hM.2.1
      have hC : ∀ i j : Fin 2, (C i j : ℕ) = e := fun i j => by simp [C]
      have e00 : (M 0 0 : ℕ) = (C 0 0 : ℕ) := by have := hC 0 0; omega
      have e01 : (M 0 1 : ℕ) = (C 0 1 : ℕ) := by have := hC 0 1; omega
      have e10 : (M 1 0 : ℕ) = (C 1 0 : ℕ) := by have := hC 1 0; omega
      have e11 : (M 1 1 : ℕ) = (C 1 1 : ℕ) := by have := hC 1 1; omega
      have hall : ∀ i j : Fin 2, (M i j : ℕ) = (C i j : ℕ) := by
        intro i j
        fin_cases i <;> fin_cases j
        · exact e00
        · exact e01
        · exact e10
        · exact e11
      funext i j
      exact Fin.ext (hall i j)
  · rw [if_neg h, Finset.card_eq_zero]
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨M, hM⟩
    have hm : IsMagic (fun i j : Fin 2 => (M i j : ℕ)) t := by
      simpa [magicSquares] using hM
    obtain ⟨hs1, hs2, hs3⟩ := two_structure t (fun i j => (M i j : ℕ)) hm.1
    have hD : (M 0 0 : ℕ) + (M 1 1 : ℕ) = t := by
      simpa [diagSum, Fin.sum_univ_two] using hm.2.1
    exact h ⟨(M 0 0 : ℕ), by omega⟩

/-- Solution for `MagicSquares.symmetric_magic_count_two`: for order two symmetry is automatic for a semi-magic square, so `S_2 = M_2`. The order-two magic count is inlined as a private helper so the file stands alone. -/
theorem solution (t : ℕ) :
    symmetricMagicCount 2 t = if 2 ∣ t then 1 else 0 := by
  classical
  have hset : symmetricMagicSquares 2 t = magicSquares 2 t := by
    ext M
    simp only [symmetricMagicSquares, magicSquares, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro h; exact h.1
    · intro h
      refine ⟨h, ?_⟩
      have hR0 : (M 0 0 : ℕ) + (M 0 1 : ℕ) = t := by
        simpa [rowSum] using h.1.1 (0 : Fin 2)
      have hC0 : (M 0 0 : ℕ) + (M 1 0 : ℕ) = t := by
        simpa [colSum] using h.1.2 (0 : Fin 2)
      have h01 : (M 0 1 : ℕ) = (M 1 0 : ℕ) := by omega
      intro i j
      fin_cases i <;> fin_cases j
      · rfl
      · exact h01
      · exact h01.symm
      · rfl
  rw [symmetricMagicCount, hset, ← magicCount, magic_count_two]
