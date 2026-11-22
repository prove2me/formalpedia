-- Prove2me | solution 1 for Lean4LPD.iPow_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:07:19.728803+00:00
-- url     : https://prove2.me/submissions/12909f81-2758-4b7b-9ff2-22ff339a16b5

module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
namespace Lean4LPD
theorem _root_.solution : iPow 3 = -Complex.I := by
  have : (3 : ZMod 4).val = 3 := rfl
  rw [iPow, this, pow_succ, pow_two, Complex.I_mul_I]
  ring
end Lean4LPD
