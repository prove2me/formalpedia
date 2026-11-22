-- Prove2me | solution 1 for Lean4LPD.PauliString.qubitXZ_eq_phase_qubitPauli
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:03.742782+00:00
-- url     : https://prove2.me/submissions/dcac203a-543d-4df6-81a0-bb94513cface

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset
namespace Lean4LPD.PauliString
theorem _root_.solution (x z : ZMod 2) :
    qubitXZ x z = iPow (-((x * z).val : ZMod 4)) • qubitPauli x z := by
  ext a b
  rw [Matrix.smul_apply, smul_eq_mul]
  have cases2 : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide
  rcases cases2 x with rfl | rfl <;> rcases cases2 z with rfl | rfl <;>
    rcases cases2 a with rfl | rfl <;> rcases cases2 b with rfl | rfl
  · change (-1 : ℂ) ^ 0 = Complex.I ^ 0 * (1)
    norm_num [pow_succ, Complex.I_sq]
  · change (0 : ℂ) = Complex.I ^ 0 * (0)
    norm_num [pow_succ, Complex.I_sq]
  · change (0 : ℂ) = Complex.I ^ 0 * (0)
    norm_num [pow_succ, Complex.I_sq]
  · change (-1 : ℂ) ^ 0 = Complex.I ^ 0 * (1)
    norm_num [pow_succ, Complex.I_sq]
  · change (-1 : ℂ) ^ 0 = Complex.I ^ 0 * (1)
    norm_num [pow_succ, Complex.I_sq]
  · change (0 : ℂ) = Complex.I ^ 0 * (0)
    norm_num [pow_succ, Complex.I_sq]
  · change (0 : ℂ) = Complex.I ^ 0 * (0)
    norm_num [pow_succ, Complex.I_sq]
  · change (-1 : ℂ) ^ 1 = Complex.I ^ 0 * (-1)
    norm_num [pow_succ, Complex.I_sq]
  · change (0 : ℂ) = Complex.I ^ 0 * (0)
    norm_num [pow_succ, Complex.I_sq]
  · change (-1 : ℂ) ^ 0 = Complex.I ^ 0 * (1)
    norm_num [pow_succ, Complex.I_sq]
  · change (-1 : ℂ) ^ 0 = Complex.I ^ 0 * (1)
    norm_num [pow_succ, Complex.I_sq]
  · change (0 : ℂ) = Complex.I ^ 0 * (0)
    norm_num [pow_succ, Complex.I_sq]
  · change (0 : ℂ) = Complex.I ^ 3 * (0)
    norm_num [pow_succ, Complex.I_sq]
  · change (-1 : ℂ) ^ 1 = Complex.I ^ 3 * (-Complex.I)
    norm_num [pow_succ, Complex.I_sq]
  · change (-1 : ℂ) ^ 0 = Complex.I ^ 3 * (Complex.I)
    norm_num [pow_succ, Complex.I_sq]
  · change (0 : ℂ) = Complex.I ^ 3 * (0)
    norm_num [pow_succ, Complex.I_sq]
end Lean4LPD.PauliString
