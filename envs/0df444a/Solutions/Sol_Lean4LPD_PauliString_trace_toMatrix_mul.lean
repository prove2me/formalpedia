-- Prove2me | solution 1 for Lean4LPD.PauliString.trace_toMatrix_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:19:02.399614+00:00
-- url     : https://prove2.me/submissions/b312177f-cf2c-4848-ae82-87bc2eb521da

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_apply_ne


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (s : PauliString n) (O : Matrix (Bits n) (Bits n) ℂ) :
    (toMatrix s * O).trace
      = iPow s.phase * ∑ b : Bits n, negOnePow (s.z ⬝ᵥ b) * O b (b + s.x) := by
  have hshift : ∀ a : Bits n, a + s.x + s.x = a := fun a => by
    rw [add_assoc, bits_add_self, add_zero]
  have hdiag : ∀ a : Bits n, (toMatrix s * O) a a
      = iPow s.phase * (negOnePow (s.z ⬝ᵥ (a + s.x)) * O (a + s.x) a) := by
    intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single (a + s.x)]
    · rw [toMatrix_apply, if_pos (hshift a).symm]
      ring
    · intro b _ hb
      refine mul_eq_zero_of_left (toMatrix_apply_ne s fun hc => hb ?_) _
      rw [hc, hshift b]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Matrix.trace, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight s.x) _ _ fun a => ?_
  rw [Matrix.diag_apply, hdiag a, Equiv.coe_addRight, hshift a]
end Lean4LPD.PauliString
