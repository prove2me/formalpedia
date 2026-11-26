-- Prove2me | solution 1 for N4Code.sum_Icc0_7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:52.543416+00:00
-- url     : https://prove2.me/submissions/3548f924-a827-439c-8884-fa546935c2a9

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
theorem _root_.solution (f : ℕ → ℕ) : (∑ i ∈ Finset.Icc 0 7, f i) =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  have h1 : (Finset.Icc 0 7 : Finset ℕ) = {0, 1, 2, 3, 4, 5, 6, 7} := by
    ext i
    constructor
    · intro hi
      simp at hi ⊢
      omega
    · intro hi
      simp at hi ⊢
      omega
  rw [h1]
  simp [Finset.sum_insert]
  ring
end N4Code
