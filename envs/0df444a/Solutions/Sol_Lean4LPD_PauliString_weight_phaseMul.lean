-- Prove2me | solution 1 for Lean4LPD.PauliString.weight_phaseMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:58:25.616327+00:00
-- url     : https://prove2.me/submissions/873a56f5-4ff6-4e3d-9989-11d14664449f

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
theorem _root_.solution (k : ZMod 4) (s : PauliString n) :
    weight (phaseMul k s) = weight s := rfl
end Lean4LPD.PauliString
