-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.opTensor_mul_leftTensor
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:47:23.393136+00:00
-- url     : https://prove2.me/submissions/4963978d-9392-4b26-91f7-00d26da1f2d8

-- Generated proof for MIPStarRE.LDT.opTensor_mul_leftTensor.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

namespace LIDT

end LIDT

open LIDT
/-!
# Quantum states and tensor placement for the low individual degree test

Core quantum-state definitions together with tensor-placement operators.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

theorem solution
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A B : _root_.LIDT.MIPStarRE.Quantum.Op ι₁) (C : _root_.LIDT.MIPStarRE.Quantum.Op ι₂) :
    _root_.LIDT.MIPStarRE.LDT.opTensor A C * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι₂) B = _root_.LIDT.MIPStarRE.LDT.opTensor (A * B) C := by
  calc
    _root_.LIDT.MIPStarRE.LDT.opTensor A C * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι₂) B
        = (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι₂) A * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι₁) C) *
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι₂) B := by
          rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
    _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι₂) A *
          (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι₁) C * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι₂) B) := by
          rw [Matrix.mul_assoc]
    _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι₂) A * _root_.LIDT.MIPStarRE.LDT.opTensor B C := by
          rw [_root_.LIDT.MIPStarRE.LDT.rightTensor_mul_leftTensor_eq_opTensor]
    _ = _root_.LIDT.MIPStarRE.LDT.opTensor (A * B) C := _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_opTensor A B C
