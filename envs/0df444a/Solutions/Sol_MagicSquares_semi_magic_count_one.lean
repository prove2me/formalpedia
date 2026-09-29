-- Prove2me | solution 1 for MagicSquares.semi_magic_count_one
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-19T05:58:03.373986+00:00
-- url     : https://prove2.me/submissions/66271456-2a15-4bd9-8d3d-303f5dc3b1b7

import Mathlib
import Definitions.Def_MagicSquares

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-- Solution for `MagicSquares.semi_magic_count_one`.

A `1 × 1` array `M` of line sum `t` has a single entry `M 0 0`, and its single row
sum is that entry; since the entries live in `Fin (t + 1)`, the equation
`(M 0 0 : ℕ) = t` pins the entry down. So every member of the filtered finset equals
the all-`t` array, which is itself a member; hence `H_1(t) = 1`.

This is the `n = 1` rung of the ladder towards `semi_magic_polynomial`: the asserted
degree `(n - 1)^2` is `0` there, matching a constant polynomial. -/
theorem solution (t : ℕ) : semiMagicCount 1 t = 1 := by
  classical
  -- the only candidate: the array whose single entry is `t`
  let M0 : Square 1 (Fin (t + 1)) := fun _ _ => ⟨t, Nat.lt_succ_self t⟩
  have hM0 : IsSemiMagic (fun i j => (M0 i j : ℕ)) t := by
    constructor
    · intro i
      fin_cases i
      simp [M0, rowSum]
    · intro j
      fin_cases j
      simp [M0, colSum]
  -- every member is `M0`: the row sum is the single entry
  have huniq : ∀ M : Square 1 (Fin (t + 1)),
      IsSemiMagic (fun i j => (M i j : ℕ)) t → M = M0 := by
    intro M hM
    have hrow : (M 0 0 : ℕ) = t := by
      have h := hM.1 (0 : Fin 1)
      simpa [IsSemiMagic, rowSum, Fin.sum_univ_one] using h
    have h0 : M 0 0 = (⟨t, Nat.lt_succ_self t⟩ : Fin (t + 1)) := Fin.ext hrow
    funext i j
    fin_cases i
    fin_cases j
    simpa [M0] using h0
  rw [semiMagicCount, semiMagicSquares, Finset.card_eq_one]
  refine ⟨M0, ?_⟩
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ M0, hM0⟩, ?_⟩
  intro M hM
  exact huniq M (by
    simpa only [semiMagicSquares, Finset.mem_filter, Finset.mem_univ, true_and] using hM)
