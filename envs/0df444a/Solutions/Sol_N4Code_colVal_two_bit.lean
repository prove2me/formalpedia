-- Prove2me | solution 1 for N4Code.colVal_two_bit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:14:15.823389+00:00
-- url     : https://prove2.me/submissions/355c5d18-eb4e-488a-a287-2e9457998101

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
theorem _root_.solution (c : Column)
    (h : ∃ a b : Fin 4, a ≠ b ∧ (c = fun j : Fin 4 => j = a ∨ j = b)) :
    colVal c = 3 ∨ colVal c = 5 ∨ colVal c = 6 ∨ colVal c = 9 ∨ colVal c = 10 ∨ colVal c = 12 := by
  rcases h with ⟨a, b, hab, hc⟩
  subst c
  have h' : ∀ a b : Fin 4, a ≠ b →
      (colVal (fun j : Fin 4 => j = a ∨ j = b) = 3 ∨
       colVal (fun j : Fin 4 => j = a ∨ j = b) = 5 ∨
       colVal (fun j : Fin 4 => j = a ∨ j = b) = 6 ∨
       colVal (fun j : Fin 4 => j = a ∨ j = b) = 9 ∨
       colVal (fun j : Fin 4 => j = a ∨ j = b) = 10 ∨
       colVal (fun j : Fin 4 => j = a ∨ j = b) = 12) := by
    decide
  exact h' a b hab
end N4Code
