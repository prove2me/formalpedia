-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.bernoulliTailOperator_leftTensor
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:44:31.317602+00:00
-- url     : https://prove2.me/submissions/ab15f3fc-2fc8-4068-8707-2d86c40e3f18

-- Generated proof for MIPStarRE.LDT.Pasting.bernoulliTailOperator_leftTensor.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Basic/QuantumState.lean. -/
/-!
# Quantum states and tensor placement for the low individual degree test

Core quantum-state definitions together with tensor-placement operators.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT













namespace PureState























end PureState























namespace QuantumState







end QuantumState




















/-- Scalar multiplication commutes with left tensor placement. -/
theorem leftTensor_smul
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : ℂ) (A : MIPStarRE.Quantum.Op ι₁) :
    c • leftTensor (ι₂ := ι₂) A = leftTensor (ι₂ := ι₂) (c • A) := by
  ext x y
  simp [leftTensor]
  ring

/-- Powers commute with left tensor placement. -/
theorem leftTensor_pow
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (n : ℕ) :
    (leftTensor (ι₂ := ι₂) A) ^ n = leftTensor (ι₂ := ι₂) (A ^ n) := by
  induction n with
  | zero => simpa using (leftTensor_one (ι₁ := ι₁) (ι₂ := ι₂)).symm
  | succ n ih =>
      rw [pow_succ, pow_succ, ih, leftTensor_mul_leftTensor]




































end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Section 12 — Definitions: tuples and operators

Tuple distributions, type abbreviations, and basic operator helpers.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution (A : _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (k degree : ℕ) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailOperator k degree (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A) =
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (_root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailOperator k degree A) := by
  unfold _root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailOperator
  rw [← _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) (Finset.Icc (degree + 1) k)
    (fun r => (Nat.choose k r : ℂ) • (A ^ r * (1 - A) ^ (k - r)))]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_pow]
  rw [show (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) - _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A =
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (1 - A) by
        rw [← _root_.LIDT.MIPStarRE.LDT.leftTensor_one (ι₁ := ι) (ι₂ := ι), _root_.LIDT.MIPStarRE.LDT.leftTensor_sub]]
  rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_pow, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor]
  exact _root_.LIDT.MIPStarRE.LDT.leftTensor_smul (ι₁ := ι) (ι₂ := ι) (Nat.choose k r : ℂ)
    (A ^ r * (1 - A) ^ (k - r))
