-- Prove2me | solution 1 for Lean4LPD.PauliString.star_mul_z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:20:42.571396+00:00
-- url     : https://prove2.me/submissions/77be06c3-6dd9-4cb0-8aba-58c708f61af2

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (s t : PauliString n) : (star s * t).z = s.z + t.z := rfl
end Lean4LPD.PauliString
