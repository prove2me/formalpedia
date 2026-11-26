-- Prove2me | solution 1 for N4Code.row0_normalize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:33.174235+00:00
-- url     : https://prove2.me/submissions/0cd5c1ab-e455-4073-af75-9c652a6fbb07

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_permEven_i

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (i j : Fin 4) (hij : i ≠ j) :
    row (normalizeCode C i j) 0 = (fun _ : Fin n => false) := by
  funext t
  have hi : (permEven i j).symm (0 : Fin 4) = i :=
    (Equiv.symm_apply_eq (e := permEven i j) (x := (0 : Fin 4)) (y := i)).mpr
      (permEven_i i j hij).symm
  unfold row colBit normalizeCode rowPermute
  rw [hi]
  by_cases hc : C t i
  · simp [row, colBit, flipCol, hc]
  · simp [row, colBit, hc]
end N4Code
