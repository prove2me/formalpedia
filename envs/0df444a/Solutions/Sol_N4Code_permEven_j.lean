-- Prove2me | solution 1 for N4Code.permEven_j
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:02.717143+00:00
-- url     : https://prove2.me/submissions/14080a90-112e-43c7-a2d1-14275222bc42

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
theorem _root_.solution (i j : Fin 4) (_hij : i ≠ j) : permEven i j j = (1 : Fin 4) := by
  unfold permEven
  calc
    permEven i j j = Equiv.swap (Equiv.swap i (0 : Fin 4) j) (1 : Fin 4)
        (Equiv.swap i (0 : Fin 4) j) := rfl
    _ = (1 : Fin 4) := Equiv.swap_apply_left (Equiv.swap i (0 : Fin 4) j) (1 : Fin 4)
end N4Code
