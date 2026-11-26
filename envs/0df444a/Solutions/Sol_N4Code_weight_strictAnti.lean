-- Prove2me | solution 1 for N4Code.weight_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:46.777996+00:00
-- url     : https://prove2.me/submissions/7f949570-d874-4efd-b228-9927626c5fe9

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
import Theorems.Thm_N4Code_weight_step

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∀ {a b : ℕ}, a < b → weight n ε b < weight n ε a := by
  intro a b hab
  have hk : b = a + (b - a - 1) + 1 := by omega
  rw [hk]
  have hiter : ∀ k : ℕ, weight n ε (a + k + 1) < weight n ε a := by
    intro k
    induction k with
    | zero =>
        simpa using weight_step hε0 hε1 a
    | succ k ih =>
        have hstep : weight n ε (a + (k + 1) + 1) < weight n ε (a + k + 1) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using weight_step hε0 hε1 (a + k + 1)
        exact lt_trans hstep ih
  exact hiter (b - a - 1)
end N4Code
