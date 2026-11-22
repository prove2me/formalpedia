-- Prove2me | solution 1 for Lean4LPD.PauliString.phase_sub_of_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:47.633048+00:00
-- url     : https://prove2.me/submissions/7db38044-18d0-4edf-bdd4-bebca642b2f3

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_iff_phase


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution {s t : PauliString n} (hs : IsSelfAdjoint s)
    (ht : IsSelfAdjoint t) (hx : s.x = t.x) (hz : s.z = t.z) :
    s.phase - t.phase = 0 ∨ s.phase - t.phase = 2 := by
  rw [isSelfAdjoint_iff_phase] at hs ht
  have h : 2 * s.phase = 2 * t.phase := by rw [← hs, ← ht, hx, hz]
  have h2 : 2 * (s.phase - t.phase) = 0 := by rw [mul_sub, h, sub_self]
  revert h2
  generalize s.phase - t.phase = d
  revert d
  decide
end Lean4LPD.PauliString
