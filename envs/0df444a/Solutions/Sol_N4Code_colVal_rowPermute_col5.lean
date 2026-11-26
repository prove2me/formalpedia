-- Prove2me | solution 1 for N4Code.colVal_rowPermute_col5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:00.266398+00:00
-- url     : https://prove2.me/submissions/c83935cc-806e-46cd-9397-561945637368

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_colVal_two_bit

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution (ρ : Equiv (Fin 4) (Fin 4)) :
    colVal (rowPermute ρ col5) = 3 ∨ colVal (rowPermute ρ col5) = 5 ∨
      colVal (rowPermute ρ col5) = 6 ∨ colVal (rowPermute ρ col5) = 9 ∨
      colVal (rowPermute ρ col5) = 10 ∨ colVal (rowPermute ρ col5) = 12 := by
  have h : rowPermute ρ col5 = fun j : Fin 4 => j = ρ.symm 1 ∨ j = ρ.symm 3 := by
    funext j
    have hv1 : (ρ j).val = 1 ↔ j = ρ.symm 1 := by
      calc
        (ρ j).val = 1 ↔ ρ j = (1 : Fin 4) :=
          (Fin.ext_iff (a := ρ j) (b := (1 : Fin 4))).symm
        _ ↔ j = ρ.symm 1 := (Equiv.eq_symm_apply ρ (x := (1 : Fin 4)) (y := j)).symm
    have hv3 : (ρ j).val = 3 ↔ j = ρ.symm 3 := by
      calc
        (ρ j).val = 3 ↔ ρ j = (3 : Fin 4) :=
          (Fin.ext_iff (a := ρ j) (b := (3 : Fin 4))).symm
        _ ↔ j = ρ.symm 3 := (Equiv.eq_symm_apply ρ (x := (3 : Fin 4)) (y := j)).symm
    simp [col5, rowPermute, hv1, hv3]
  refine colVal_two_bit (rowPermute ρ col5) ⟨ρ.symm 1, ρ.symm 3, ?_, h⟩
  -- ρ⁻¹ 1 ≠ ρ⁻¹ 3 — injective
  intro hEq
  have : (1 : Fin 4) = (3 : Fin 4) := ρ.symm.injective hEq
  exact (by decide : (1 : Fin 4) ≠ (3 : Fin 4)) this
end N4Code
