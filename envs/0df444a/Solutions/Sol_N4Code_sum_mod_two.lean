-- Prove2me | solution 1 for N4Code.sum_mod_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:38.811782+00:00
-- url     : https://prove2.me/submissions/708733e9-5632-40f1-b673-2498a98af0c4

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
theorem _root_.solution {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∑ t ∈ s, f t) % 2 = (∑ t ∈ s, f t % 2) % 2 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s' has ih
    rw [Finset.sum_insert has, Finset.sum_insert has, Nat.add_mod, ih]
    simp [Nat.add_mod]
end N4Code
