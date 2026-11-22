-- Prove2me | solution 1 for Lean4LPD.PauliString.mul_eq_phaseMul_sympForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:06:05.236796+00:00
-- url     : https://prove2.me/submissions/4a1ef4b4-4690-4660-a15b-4e758e84a6b2

module
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
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
theorem _root_.solution (s t : PauliString n) :
    s * t = phaseMul (signPhase (sympForm s t)) (t * s) := by
  refine ext' ?_ ?_ ?_
  · simp [add_comm]
  · simp [add_comm]
  · simp only [mul_phase, phaseMul_phase, sympForm, signPhase_add]
    rw [dotProduct_comm s.x t.z]
    rw [show t.phase + s.phase + signPhase (t.z ⬝ᵥ s.x)
          + (signPhase (t.z ⬝ᵥ s.x) + signPhase (s.z ⬝ᵥ t.x))
        = s.phase + t.phase + signPhase (s.z ⬝ᵥ t.x)
          + (signPhase (t.z ⬝ᵥ s.x) + signPhase (t.z ⬝ᵥ s.x)) by ring]
    simp
end Lean4LPD.PauliString
