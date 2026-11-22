-- Prove2me | solution 1 for Lean4LPD.PauliString.isSelfAdjoint_Y1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:13:09.803112+00:00
-- url     : https://prove2.me/submissions/9bd6515b-ff22-433b-8ea4-cedca7c91e27

module
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_iff_phase

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution : IsSelfAdjoint Y1 := isSelfAdjoint_iff_phase.2 (by decide)
end Lean4LPD.PauliString
