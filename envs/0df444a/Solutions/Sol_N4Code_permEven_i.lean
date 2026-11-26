-- Prove2me | solution 1 for N4Code.permEven_i
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:40.515565+00:00
-- url     : https://prove2.me/submissions/dfa22ecb-e7f8-4df5-8041-7a0e6d131db5

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
theorem _root_.solution (i j : Fin 4) (hij : i ≠ j) : permEven i j i = (0 : Fin 4) := by
  unfold permEven
  have he1i : Equiv.swap i (0 : Fin 4) i = (0 : Fin 4) := Equiv.swap_apply_left i (0 : Fin 4)
  have he1j0 : Equiv.swap i (0 : Fin 4) j ≠ (0 : Fin 4) := by
    rw [Equiv.swap_apply_def]
    by_cases hji : j = i
    · exfalso
      exact hij hji.symm
    · by_cases hj0 : j = (0 : Fin 4)
      · have hi0 : i ≠ (0 : Fin 4) := by
          intro h
          exact hij (h.trans hj0.symm)
        rw [hj0]
        have h0i : (0 : Fin 4) ≠ i := fun h => hji (h.symm.trans hj0.symm).symm
        have hvalue : (if (0 : Fin 4) = i then (0 : Fin 4)
            else if (0 : Fin 4) = (0 : Fin 4) then i else (0 : Fin 4)) = i := by
          simp [h0i]
        rw [hvalue]
        exact hi0
      · simp [hj0, hji]
  calc
    permEven i j i = Equiv.swap (Equiv.swap i (0 : Fin 4) j) (1 : Fin 4)
        (Equiv.swap i (0 : Fin 4) i) := rfl
    _ = Equiv.swap (Equiv.swap i (0 : Fin 4) j) (1 : Fin 4) (0 : Fin 4) := by rw [he1i]
    _ = (0 : Fin 4) := by
      have h01 : (0 : Fin 4) ≠ (1 : Fin 4) := by decide
      exact Equiv.swap_apply_of_ne_of_ne (fun h => he1j0 h.symm) h01
end N4Code
