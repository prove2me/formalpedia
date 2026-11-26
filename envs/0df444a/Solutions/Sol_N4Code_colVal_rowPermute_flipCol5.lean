-- Prove2me | solution 1 for N4Code.colVal_rowPermute_flipCol5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:08.39565+00:00
-- url     : https://prove2.me/submissions/7e2ac4ee-b52e-4582-840c-2bce2df5563f

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_colVal_two_bit
import Theorems.Thm_N4Code_flipCol_col5_val

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution (ρ : Equiv (Fin 4) (Fin 4)) :
    colVal (rowPermute ρ (flipCol col5)) = 3 ∨ colVal (rowPermute ρ (flipCol col5)) = 5 ∨
      colVal (rowPermute ρ (flipCol col5)) = 6 ∨ colVal (rowPermute ρ (flipCol col5)) = 9 ∨
      colVal (rowPermute ρ (flipCol col5)) = 10 ∨ colVal (rowPermute ρ (flipCol col5)) = 12 := by
  have h : rowPermute ρ (flipCol col5) = fun j : Fin 4 => j = ρ.symm 0 ∨ j = ρ.symm 2 := by
    funext j
    have hb0 : (ρ j = (0 : Fin 4)) ↔ j = ρ.symm 0 :=
      (Equiv.eq_symm_apply ρ (x := (0 : Fin 4)) (y := j)).symm
    have hb2 : (ρ j = (2 : Fin 4)) ↔ j = ρ.symm 2 :=
      (Equiv.eq_symm_apply ρ (x := (2 : Fin 4)) (y := j)).symm
    calc
      rowPermute ρ (flipCol col5) j = !(col5 (ρ j)) := by simp [rowPermute, flipCol]
      _ = decide (ρ j = (0 : Fin 4) ∨ ρ j = (2 : Fin 4)) := by
        simpa using (flipCol_col5_val (ρ j))
      _ = decide (j = ρ.symm 0 ∨ j = ρ.symm 2) := by
        simp [hb0, hb2]
  refine colVal_two_bit (rowPermute ρ (flipCol col5)) ⟨ρ.symm 0, ρ.symm 2, ?_, h⟩
  -- ρ⁻¹ 0 ≠ ρ⁻¹ 2 — injective
  intro hEq
  have : (0 : Fin 4) = (2 : Fin 4) := ρ.symm.injective hEq
  exact (by decide : (0 : Fin 4) ≠ (2 : Fin 4)) this
end N4Code
