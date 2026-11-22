-- Prove2me | solution 1 for Lean4LPD.PauliString.isSelfAdjoint_iff_mul_self_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:08:11.47353+00:00
-- url     : https://prove2.me/submissions/8792b35b-03c3-4fd8-afe3-73ea331a2c8d

module
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Theorems.Thm_Lean4LPD_PauliString_star_eq_inv

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution {s : PauliString n} :
    IsSelfAdjoint s ↔ s * s = 1 := by
  rw [IsSelfAdjoint, star_eq_inv, inv_eq_iff_mul_eq_one]
end Lean4LPD.PauliString
