-- Prove2me | solution 1 for N4Code.min4_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:10.03421+00:00
-- url     : https://prove2.me/submissions/9144c8df-0d94-4734-9554-fe4b659b9d7b

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution (a : Fin 4 → ℕ) :
    min (a 0) (min (a 1) (min (a 2) (a 3))) = (Finset.univ.image a).min' (by simp) := by
  apply le_antisymm
  · apply Finset.le_min' (Finset.univ.image a) (by simp) (min (a 0) (min (a 1) (min (a 2) (a 3))))
    intro y hy
    rcases (Finset.mem_image.mp hy) with ⟨j, _hj, hjy⟩
    rw [← hjy]
    fin_cases j
    · exact Nat.min_le_left _ _
    · exact (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
    · exact (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (Nat.min_le_left _ _))
    · exact (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (Nat.min_le_right _ _))
  · exact le_min (Finset.min'_le (Finset.univ.image a) (a 0) (by simp))
      (le_min (Finset.min'_le (Finset.univ.image a) (a 1) (by simp))
        (le_min (Finset.min'_le (Finset.univ.image a) (a 2) (by simp))
          (Finset.min'_le (Finset.univ.image a) (a 3) (by simp))))
end N4Code
