-- Prove2me | solution 1 for Lean4LPD.PauliString.sympForm_phaseMul_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:58:08.521433+00:00
-- url     : https://prove2.me/submissions/c5443146-ff33-45a1-b8e6-358d552280fc

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
theorem _root_.solution (k : ZMod 4) (s t : PauliString n) :
    sympForm (phaseMul k s) t = sympForm s t := rfl
end Lean4LPD.PauliString
