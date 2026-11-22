-- Prove2me | solution 1 for Lean4LPD.PauliString.star_mul_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:14:46.986912+00:00
-- url     : https://prove2.me/submissions/9800e8f3-8cde-47e1-998d-5ae07fdce0f9

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
theorem _root_.solution (s t : PauliString n) : (star s * t).x = s.x + t.x := rfl
end Lean4LPD.PauliString
