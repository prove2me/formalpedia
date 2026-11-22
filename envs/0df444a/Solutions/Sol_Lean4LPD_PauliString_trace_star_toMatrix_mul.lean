-- Prove2me | solution 1 for Lean4LPD.PauliString.trace_star_toMatrix_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:52.030263+00:00
-- url     : https://prove2.me/submissions/3272cb96-92ba-4692-a836-fa47c2d7e060

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Theorems.Thm_Lean4LPD_PauliString_trace_toMatrix_of_x_ne_zero
public import Theorems.Thm_Lean4LPD_PauliString_trace_toMatrix_of_x_eq_zero
public import Theorems.Thm_Lean4LPD_PauliString_star_mul_x
public import Theorems.Thm_Lean4LPD_PauliString_star_mul_z
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_mul
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_star
public import Theorems.Thm_Lean4LPD_bits_add_eq_zero_iff


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (s t : PauliString n) :
    (star (toMatrix s) * toMatrix t).trace
      = if s.x = t.x ∧ s.z = t.z then (2 : ℂ) ^ n * iPow (star s * t).phase else 0 := by
  rw [toMatrix_star, toMatrix_mul]
  by_cases hx : s.x = t.x
  · have hx0 : (star s * t).x = 0 := by
      rw [star_mul_x]; exact bits_add_eq_zero_iff.2 hx
    rw [trace_toMatrix_of_x_eq_zero hx0, char_sum, star_mul_z]
    by_cases hz : s.z = t.z
    · rw [if_pos (bits_add_eq_zero_iff.2 hz), if_pos ⟨hx, hz⟩]
      ring
    · rw [if_neg (fun h => hz (bits_add_eq_zero_iff.1 h)),
        if_neg (fun h => hz h.2)]
      ring
  · have hx0 : (star s * t).x ≠ 0 := fun h => hx (bits_add_eq_zero_iff.1 (by rwa [star_mul_x] at h))
    rw [trace_toMatrix_of_x_ne_zero hx0, if_neg (fun h => hx h.1)]
end Lean4LPD.PauliString
