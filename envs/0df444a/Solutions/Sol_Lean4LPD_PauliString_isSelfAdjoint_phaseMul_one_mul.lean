-- Prove2me | solution 1 for Lean4LPD.PauliString.isSelfAdjoint_phaseMul_one_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:09:13.399639+00:00
-- url     : https://prove2.me/submissions/cfa1b05b-82d7-4774-aa46-a5de70a36080

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
public import Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_iff_phase
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
section
@[expose] public section
namespace Lean4LPD
private lemma two_mul_signPhase (a : ZMod 2) : 2 * signPhase a = 0 := by revert a; decide
namespace PauliString
variable {n : ℕ} {s t u : PauliString n}
end PauliString
end Lean4LPD
end
end

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution {G s : PauliString n} (hG : IsSelfAdjoint G)
    (hs : IsSelfAdjoint s) (h : sympForm G s = 1) : IsSelfAdjoint (phaseMul 1 (G * s)) := by
  rw [isSelfAdjoint_iff_phase] at hG hs ⊢
  have e1 : signPhase (G.z ⬝ᵥ s.x) + signPhase (s.z ⬝ᵥ G.x) = 2 := by
    rw [← signPhase_add, add_comm (G.z ⬝ᵥ s.x) _, dotProduct_comm s.z G.x]
    rw [show G.x ⬝ᵥ s.z + G.z ⬝ᵥ s.x = sympForm G s from rfl, h, signPhase_one]
  have e2 : 2 * signPhase (G.z ⬝ᵥ s.x) = 0 := two_mul_signPhase _
  simp only [phaseMul_x, phaseMul_z, phaseMul_phase, mul_x, mul_z, mul_phase,
    add_dotProduct, dotProduct_add, signPhase_add]
  linear_combination hG + hs + e1 - e2
end Lean4LPD.PauliString
