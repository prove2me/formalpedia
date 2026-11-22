-- Prove2me | solution 1 for Lean4LPD.PauliString.anticommute_iff_sympForm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:07:11.586803+00:00
-- url     : https://prove2.me/submissions/cf34a92b-a4d7-4152-8c0b-a06f16e1cf94

module
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_phaseMul_iff
public import Theorems.Thm_Lean4LPD_PauliString_mul_eq_phaseMul_sympForm
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_phaseMul_iff

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (s t : PauliString n) :
    s * t = phaseMul 2 (t * s) ↔ sympForm s t = 1 := by
  rw [mul_eq_phaseMul_sympForm s t, phaseMul_eq_phaseMul_iff]
  exact (by decide : ∀ a : ZMod 2, signPhase a = 2 ↔ a = 1) _
end Lean4LPD.PauliString
