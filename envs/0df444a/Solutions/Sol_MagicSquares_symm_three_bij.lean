-- Prove2me | solution 1 for MagicSquares.symm_three_bij
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-18T14:05:48.818562+00:00
-- url     : https://prove2.me/submissions/0e540dab-b622-4f4c-a129-c7bd677d9816

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresSpecial3

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/- Auxiliary lemmas for `MagicSquares.symm_three_bij`. -/
namespace MagicSquaresSpecial3Aux

/-- A symmetric `3 × 3` magic square of line sum `3 * e` is determined by its
top-left corner. Symmetry identifies `M 0 1 = M 1 0`, `M 0 2 = M 2 0` and
`M 1 2 = M 2 1`, leaving five free cells; the anti-diagonal reads
`2 (M 0 2) + (M 1 1) = 3 e`, which forces `M 0 2 = M 1 1 = e`, and the rows then
determine everything else from `a = M 0 0`. -/
theorem classify (e : ℕ) (M : Square 3 ℕ)
    (hM : IsMagic M (3 * e)) (hsym : IsSymmetric M) :
    M = symmMagic3 e (M 0 0) := by
  have hR0 : M 0 0 + M 0 1 + M 0 2 = 3 * e := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (0 : Fin 3)
  have hR1 : M 1 0 + M 1 1 + M 1 2 = 3 * e := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (1 : Fin 3)
  have hR2 : M 2 0 + M 2 1 + M 2 2 = 3 * e := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (2 : Fin 3)
  have hD : M 0 0 + M 1 1 + M 2 2 = 3 * e := by
    simpa [diagSum, Fin.sum_univ_three] using hM.2.1
  have hA : M 0 2 + M 1 1 + M 2 0 = 3 * e := by
    simpa [antiDiagSum, Fin.sum_univ_three] using hM.2.2
  have h01 : M 0 1 = M 1 0 := hsym (0 : Fin 3) (1 : Fin 3)
  have h02 : M 0 2 = M 2 0 := hsym (0 : Fin 3) (2 : Fin 3)
  have h12 : M 1 2 = M 2 1 := hsym (1 : Fin 3) (2 : Fin 3)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symmMagic3] <;> omega

/-- `symmMagic3 e a` is a magic square of line sum `3 * e` for every admissible
corner parameter `a ≤ 2 * e`. -/
theorem symmMagic3_magic (e a : ℕ) (ha : a ≤ 2 * e) :
    IsMagic (symmMagic3 e a) (3 * e) := by
  refine ⟨⟨fun i => ?_, fun j => ?_⟩, ?_, ?_⟩
  · fin_cases i <;> simp [rowSum, symmMagic3, Fin.sum_univ_three] <;> omega
  · fin_cases j <;> simp [colSum, symmMagic3, Fin.sum_univ_three] <;> omega
  · simp [diagSum, symmMagic3, Fin.sum_univ_three]
    omega
  · simp [antiDiagSum, symmMagic3, Fin.sum_univ_three]
    omega

/-- `symmMagic3 e a` is symmetric for every `a`. -/
theorem symmMagic3_symmetric (e a : ℕ) : IsSymmetric (symmMagic3 e a) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [symmMagic3]

end MagicSquaresSpecial3Aux

open MagicSquaresSpecial3Aux

/-- Solution for `MagicSquares.symm_three_bij`.

The corner parameter `a = M 0 0` is a bijection from the symmetric magic squares
of order three and line sum `3 * e` onto the admissible set
`symmParamSet e = {0, 1, …, 2e}`:

* *well defined.* By `classify`, a symmetric magic square of line sum `3 * e` is
  `symmMagic3 e (M 0 0)`, whose `(0,1)` entry is `2e - a`; the row `0` identity
  `a + (2e - a) + e = 3e` is satisfiable in `ℕ` only for `a ≤ 2e`.
* *injective.* Two such squares with the same `M 0 0` are both `symmMagic3 e a`.
* *surjective.* For `a ≤ 2e`, `symmMagic3 e a` is a magic square of line sum
  `3 * e` (`symmMagic3_magic`) and symmetric (`symmMagic3_symmetric`); all its
  entries are at most `2e ≤ 3e`, so it may be read over `Fin (3e+1)`, and its
  top-left entry is `a` again.

Hence `symmetricMagicCount 3 (3 * e) = symmParamCount e`. -/
theorem solution (e : ℕ) : symmetricMagicCount 3 (3 * e) = symmParamCount e := by
  classical
  rw [symmetricMagicCount, symmParamCount, symmParamSet]
  change
    (Finset.univ.filter (fun M : Square 3 (Fin (3 * e + 1)) =>
      IsMagic (fun i j => (M i j : ℕ)) (3 * e) ∧
        IsSymmetric (fun i j => (M i j : ℕ)))).card =
    (Finset.range (2 * e + 1)).card
  refine Finset.card_bij (fun M _ => (M 0 0 : ℕ)) ?h_mem ?h_inj ?h_surj
  · intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    simp only [Finset.mem_range]
    have hEq := classify e (fun i j => (M i j : ℕ)) hM.1 hM.2
    have hR0 : (M 0 0 : ℕ) + (M 0 1 : ℕ) + (M 0 2 : ℕ) = 3 * e := by
      simpa [rowSum, Fin.sum_univ_three] using hM.1.1.1 (0 : Fin 3)
    have h01 : (M 0 1 : ℕ) = 2 * e - (M 0 0 : ℕ) := by
      have h := congr_fun (congr_fun hEq (0 : Fin 3)) (1 : Fin 3)
      simpa [symmMagic3] using h
    have h02 : (M 0 2 : ℕ) = e := by
      have h := congr_fun (congr_fun hEq (0 : Fin 3)) (2 : Fin 3)
      simpa [symmMagic3] using h
    omega
  · intro M₁ hM₁ M₂ hM₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM₁ hM₂
    have hEq₁ := classify e (fun i j => (M₁ i j : ℕ)) hM₁.1 hM₁.2
    have hEq₂ := classify e (fun i j => (M₂ i j : ℕ)) hM₂.1 hM₂.2
    have ha : (M₁ 0 0 : ℕ) = (M₂ 0 0 : ℕ) := heq
    ext i j
    calc
      (M₁ i j : ℕ) = symmMagic3 e (M₁ 0 0 : ℕ) i j := by
        exact congr_fun (congr_fun hEq₁ i) j
      _ = symmMagic3 e (M₂ 0 0 : ℕ) i j := by rw [ha]
      _ = (M₂ i j : ℕ) := by
        exact (congr_fun (congr_fun hEq₂ i) j).symm
  · intro a ha
    simp only [Finset.mem_range] at ha
    have ha' : a ≤ 2 * e := by omega
    let M : Square 3 (Fin (3 * e + 1)) :=
      fun i j => ⟨symmMagic3 e a i j, by
        fin_cases i <;> fin_cases j <;> simp [symmMagic3] <;> omega⟩
    refine ⟨M, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · have hM : (fun i j => (M i j : ℕ)) = symmMagic3 e a := by
          ext i j
          simp [M]
        rw [hM]
        exact symmMagic3_magic e a ha'
      · have hM : (fun i j => (M i j : ℕ)) = symmMagic3 e a := by
          ext i j
          simp [M]
        rw [hM]
        exact symmMagic3_symmetric e a
    · simp [M, symmMagic3]
