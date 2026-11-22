-- Prove2me | solution 1 for Lean4LPD.PauliString.isSelfAdjoint_iff_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:06:03.71855+00:00
-- url     : https://prove2.me/submissions/dbb0d18e-334f-415c-8bb0-b526f0968520

module
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Theorems.Thm_Lean4LPD_PauliString_inv_phase
public import Theorems.Thm_Lean4LPD_PauliString_star_eq_inv
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_self
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_x
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_z
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_phase
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_left
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_self_right
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_zero
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_phaseMul_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_self_iff
attribute [local simp] Lean4LPD.PauliString.sympForm_self
attribute [local simp] Lean4LPD.PauliString.phaseMul_x
attribute [local simp] Lean4LPD.PauliString.phaseMul_z
attribute [local simp] Lean4LPD.PauliString.phaseMul_phase
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_right
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_left
attribute [local simp] Lean4LPD.PauliString.sympForm_mul_self_right
attribute [local simp] Lean4LPD.PauliString.phaseMul_zero
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_phaseMul_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_self_iff

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution {s : PauliString n} :
    IsSelfAdjoint s ↔ signPhase (s.z ⬝ᵥ s.x) = 2 * s.phase := by
  rw [IsSelfAdjoint, star_eq_inv]
  constructor
  · intro h
    have hp := congrArg PauliString.phase h
    simp only [inv_phase] at hp
    calc signPhase (s.z ⬝ᵥ s.x)
        = s.phase + (-s.phase + signPhase (s.z ⬝ᵥ s.x)) := by ring
      _ = s.phase + s.phase := by rw [hp]
      _ = 2 * s.phase := by ring
  · intro h
    refine ext' rfl rfl ?_
    change -s.phase + signPhase (s.z ⬝ᵥ s.x) = s.phase
    rw [h]; ring
end Lean4LPD.PauliString
