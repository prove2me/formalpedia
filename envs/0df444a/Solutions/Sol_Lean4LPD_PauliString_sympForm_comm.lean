-- Prove2me | solution 1 for Lean4LPD.PauliString.sympForm_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:59.379066+00:00
-- url     : https://prove2.me/submissions/6e36ea20-ad2e-4ce8-b6a5-f4fe8e08a2fd

module
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (s t : PauliString n) : sympForm s t = sympForm t s := by
  simp only [sympForm]
  rw [dotProduct_comm s.x t.z, dotProduct_comm s.z t.x, add_comm]
end Lean4LPD.PauliString
