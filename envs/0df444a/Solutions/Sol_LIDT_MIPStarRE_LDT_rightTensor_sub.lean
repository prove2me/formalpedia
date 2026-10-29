-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.rightTensor_sub
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:47:23.367764+00:00
-- url     : https://prove2.me/submissions/f8e2cd90-7aa9-4f96-80d9-9704141414de

-- Generated proof for MIPStarRE.LDT.rightTensor_sub.
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
    (A B : _root_.LIDT.MIPStarRE.Quantum.Op ι₂) :
    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι₁) A - _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι₁) B =
      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι₁) (A - B) := by
  simpa [_root_.LIDT.MIPStarRE.LDT.rightTensor, _root_.LIDT.MIPStarRE.LDT.opTensor] using
    (_root_.LIDT.MIPStarRE.Quantum.kronecker_sub_right
      (A := (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι₁)) (B₁ := A) (B₂ := B))
