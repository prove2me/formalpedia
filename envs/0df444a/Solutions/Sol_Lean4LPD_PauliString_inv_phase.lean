-- Prove2me | solution 1 for Lean4LPD.PauliString.inv_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:02:06.544103+00:00
-- url     : https://prove2.me/submissions/192da847-f80c-40f5-ad1b-5bd67e676a4d

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
theorem _root_.solution (s : PauliString n) :
    s⁻¹.phase = -s.phase + signPhase (s.z ⬝ᵥ s.x) := rfl
end Lean4LPD.PauliString
