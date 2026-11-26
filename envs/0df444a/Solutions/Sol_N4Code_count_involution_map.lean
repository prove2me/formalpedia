-- Prove2me | solution 1 for N4Code.count_involution_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:13.090016+00:00
-- url     : https://prove2.me/submissions/793f8789-15a0-4fa1-9b17-b222d28bb8ad

import Definitions.Def_N4Code_Definitions
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Definitions.Def_N4Code_Basic

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (gv : ℕ → ℕ)
    (hcol : ∀ t : Fin n, colVal (C' t) = gv (colVal (C t)))
    (hIdem : ∀ i : ℕ, gv (gv i) = i) (i : ℕ) :
    count C' i = count C (gv i) := by
  unfold count
  apply Finset.sum_congr rfl
  intro t _
  rw [hcol t]
  have hiff : gv (colVal (C t)) = i ↔ colVal (C t) = gv i := by
    constructor
    · intro h
      have h1 := congrArg gv h
      rwa [hIdem] at h1
    · intro h
      rw [h]
      exact hIdem i
  by_cases h : gv (colVal (C t)) = i
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (hiff.not.mp h)]
end N4Code
