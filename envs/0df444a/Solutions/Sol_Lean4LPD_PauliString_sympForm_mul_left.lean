-- Prove2me | solution 1 for Lean4LPD.PauliString.sympForm_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:13:01.062991+00:00
-- url     : https://prove2.me/submissions/be376348-37b1-4346-9788-f63908d3f7aa

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
theorem _root_.solution (s t u : PauliString n) :
    sympForm (s * t) u = sympForm s u + sympForm t u := by
  simp only [sympForm, mul_x, mul_z, add_dotProduct]
  ring
end Lean4LPD.PauliString
