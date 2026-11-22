-- Prove2me | solution 1 for Lean4LPD.PauliString.site_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:58:24.305515+00:00
-- url     : https://prove2.me/submissions/7d16aa23-7ef5-4327-8e05-ba4bff78310f

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
theorem _root_.solution (s t : PauliString n) (i : Fin n) :
    site (s * t) i = site s i + site t i := rfl
end Lean4LPD.PauliString
