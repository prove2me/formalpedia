-- Prove2me | solution 1 for N4Code.Icc0_7_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:36.542748+00:00
-- url     : https://prove2.me/submissions/003f15f7-f96a-46be-8ac7-3acc644daa37

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution : (Finset.Icc 0 7 : Finset ℕ) = {0, 5, 6} ∪ {1, 2, 3, 4, 7} := by
  ext i
  constructor
  · intro hi
    simp at hi
    have hi' : i = 0 ∨ i = 5 ∨ i = 6 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 7 := by omega
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · intro hi
    rcases (Finset.mem_union.mp hi) with hi' | hi'
    · simp at hi' ⊢
      omega
    · simp at hi' ⊢
      omega
end N4Code
