-- Prove2me | solution 1 for Lean4LPD.PauliString.site_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:58:24.683665+00:00
-- url     : https://prove2.me/submissions/1d41ccdc-55de-44f1-b4a8-52adb9192d4f

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}
namespace Lean4LPD.PauliString
theorem _root_.solution (i : Fin n) : site (1 : PauliString n) i = 0 := rfl
end Lean4LPD.PauliString
