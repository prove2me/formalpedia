-- Prove2me | solution 1 for Lean4LPD.PauliString.phaseMul_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:58:07.748556+00:00
-- url     : https://prove2.me/submissions/6e9ed8f0-5da7-447d-a69b-341406193ec0

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
theorem _root_.solution (k : ZMod 4) (s : PauliString n) :
    (phaseMul k s).phase = s.phase + k := rfl
end Lean4LPD.PauliString
