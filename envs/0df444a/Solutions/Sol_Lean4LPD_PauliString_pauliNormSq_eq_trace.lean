-- Prove2me | solution 1 for Lean4LPD.PauliString.pauliNormSq_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:35.130227+00:00
-- url     : https://prove2.me/submissions/50cade5b-96dd-44c2-b22d-52536eb7d083

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (O : Matrix (Bits n) (Bits n) ℂ) :
    ((pauliNormSq O : ℝ) : ℂ) = ((2 : ℂ) ^ n)⁻¹ * (star O * O).trace := by
  have h : (star O * O).trace = ∑ a : Bits n, ∑ b : Bits n, ((‖O a b‖ : ℝ) : ℂ) ^ 2 := by
    rw [Matrix.trace]
    rw [Finset.sum_comm (s := (univ : Finset (Bits n))) (t := (univ : Finset (Bits n)))
      (f := fun a b => ((‖O a b‖ : ℝ) : ℂ) ^ 2)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.star_apply, ← Complex.mul_conj' (O b a), RCLike.star_def, mul_comm]
  rw [pauliNormSq, h]
  push_cast
  rw [Finset.mul_sum]
end Lean4LPD.PauliString
