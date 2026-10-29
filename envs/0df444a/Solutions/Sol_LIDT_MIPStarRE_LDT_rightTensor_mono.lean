-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.rightTensor_mono
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:47:23.095578+00:00
-- url     : https://prove2.me/submissions/2f04e31f-b452-40b7-8170-498e7febb8e7

-- Generated proof for MIPStarRE.LDT.rightTensor_mono.
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
    {B₁ B₂ : _root_.LIDT.MIPStarRE.Quantum.Op ι₂} (hB : B₁ ≤ B₂) :
    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι₁) B₁ ≤ _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι₁) B₂ := by
  exact _root_.LIDT.MIPStarRE.LDT.opTensor_mono_right Matrix.PosSemidef.one.nonneg hB
