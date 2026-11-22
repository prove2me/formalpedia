-- Prove2me | solution 1 for Lean4LPD.PauliString.trace_star_toMatrix_mul_phaseMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:39.410882+00:00
-- url     : https://prove2.me/submissions/96c0f29b-87f1-429d-975d-e9f7dcc1c83b

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Theorems.Thm_Lean4LPD_PauliString_trace_star_toMatrix_mul

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (k : ZMod 4) (s : PauliString n) :
    (star (toMatrix s) * toMatrix (phaseMul k s)).trace = (2 : ℂ) ^ n * iPow k := by
  have hp : (star s * phaseMul k s).phase = k := by
    have h : (star s * phaseMul k s).phase
        = (-s.phase + signPhase (s.z ⬝ᵥ s.x)) + (s.phase + k)
          + signPhase (s.z ⬝ᵥ s.x) := rfl
    rw [h, show (-s.phase + signPhase (s.z ⬝ᵥ s.x)) + (s.phase + k) + signPhase (s.z ⬝ᵥ s.x)
        = k + (signPhase (s.z ⬝ᵥ s.x) + signPhase (s.z ⬝ᵥ s.x)) by ring,
      signPhase_add_self, add_zero]
  rw [trace_star_toMatrix_mul, if_pos ⟨rfl, rfl⟩, hp]
end Lean4LPD.PauliString
