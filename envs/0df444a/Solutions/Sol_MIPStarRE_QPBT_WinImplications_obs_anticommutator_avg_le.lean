-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.obs_anticommutator_avg_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:08:33.257372+00:00
-- url     : https://prove2.me/submissions/13ada014-a747-421c-8eef-14f72f4ddec1

-- Generated proof for MIPStarRE.QPBT.WinImplications.obs_anticommutator_avg_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_norm_product_transfer_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Games/Defs.lean. -/
/-!
# Games, tensor-product strategies, and value

This file provides the finite game carrier used by the Pauli basis test.  Pure
states are vectors in `EuclideanSpace`, and POVMs use the project's matrix
`Measurement` structure.

## References

The source-facing nodes are blueprint `def:game`, `def:povm-conventions`,
`def:tensor-product-strategy`, and `def:tensor-product-value`.
The paper origin is `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:10-57`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum



attribute [instance] _root_.MIPStarRE.QPBT.Game.questionAFintype _root_.MIPStarRE.QPBT.Game.questionBFintype
  _root_.MIPStarRE.QPBT.Game.answerAFintype _root_.MIPStarRE.QPBT.Game.answerBFintype _root_.MIPStarRE.QPBT.Game.questionADecidableEq
  _root_.MIPStarRE.QPBT.Game.questionBDecidableEq _root_.MIPStarRE.QPBT.Game.answerADecidableEq _root_.MIPStarRE.QPBT.Game.answerBDecidableEq









attribute [instance] _root_.MIPStarRE.QPBT.Strategy.ιAFintype _root_.MIPStarRE.QPBT.Strategy.ιBFintype
  _root_.MIPStarRE.QPBT.Strategy.ιADecidableEq _root_.MIPStarRE.QPBT.Strategy.ιBDecidableEq



/-! ### Algebra of the tensor placement

The shared tensor-placement API.  These identities are used both by the perfect
Magic Square strategy (blueprint `thm:ms-from-ac`) and by the rigidity transfer
step (blueprint `thm:ms-rigidity`), so they live
with the definition rather than in either development. -/











/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
is additive in the right factor. -/
theorem heteroKron_add_right {ιA ιB : Type*} (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B C : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron A (B + C) = _root_.MIPStarRE.QPBT.heteroKron A B + _root_.MIPStarRE.QPBT.heteroKron A C := by
  ext p q
  simp [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, mul_add]









/- The Euclidean linear map is the shared action used by the value and distance
functionals.  Keeping it at the Euclidean-space level avoids accidentally
using the function-space supremum norm of `Matrix.mulVec`. -/








































end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/AnticommutingObs.lean. -/
/-!
# Approximate anticommutation of the point observables on anticommuting tuples

This module carries out the anticommuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`. The Magic Square
approximate anticommutation of the variable observables is read back from the
projective dilation on which it is proved, and transported to Alice's point
observables through item 7 of `lem:qld-win-implications`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reading the dilation back on the original space -/













/-! ## The Magic Square anticommutation on the undilated strategy -/













/-! ## Reflections and the product transfer -/

/-- The tensor placement respects the adjoint. Formalization-only support for
`fact:add-a-proj`, blueprint `ch12_qpbt_games.tex:305-321`. -/
theorem heteroKron_conjTranspose {ιA ιB : Type*} (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    (_root_.MIPStarRE.QPBT.heteroKron A B)ᴴ = _root_.MIPStarRE.QPBT.heteroKron Aᴴ Bᴴ := by
  ext i j
  simp [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.conjTranspose_apply]

/-- Placing an isometry on the first factor gives an isometry.
Formalization-only support for `fact:add-a-proj`, blueprint
`ch12_qpbt_games.tex:305-321`. -/
theorem heteroKron_left_isometry {ιA ιB : Type*} [DecidableEq ιA]
    [DecidableEq ιB] [Fintype ιA] [Fintype ιB] (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA)
    (hA : Aᴴ * A = 1) :
    (_root_.MIPStarRE.QPBT.heteroKron A (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB))ᴴ * _root_.MIPStarRE.QPBT.heteroKron A 1 = 1 := by
  rw [_root_.MIPStarRE.QPBT.WinImplications.heteroKron_conjTranspose, _root_.MIPStarRE.QPBT.heteroKron_mul, hA, Matrix.conjTranspose_one,
    one_mul, _root_.MIPStarRE.QPBT.heteroKron_one_one]

/-- Placing an isometry on the second factor gives an isometry.
Formalization-only support for `fact:add-a-proj`, blueprint
`ch12_qpbt_games.tex:305-321`. -/
theorem heteroKron_right_isometry {ιA ιB : Type*} [DecidableEq ιA]
    [DecidableEq ιB] [Fintype ιA] [Fintype ιB] (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB)
    (hB : Bᴴ * B = 1) :
    (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) B)ᴴ * _root_.MIPStarRE.QPBT.heteroKron 1 B = 1 := by
  rw [_root_.MIPStarRE.QPBT.WinImplications.heteroKron_conjTranspose, _root_.MIPStarRE.QPBT.heteroKron_mul, hB, Matrix.conjTranspose_one,
    one_mul, _root_.MIPStarRE.QPBT.heteroKron_one_one]





/-! ## From the Magic Square variables to the point observables -/









/-! ## The anticommuting half of the twisted commutation -/





















end WinImplications

end

end MIPStarRE.QPBT

/-!
# Approximate anticommutation of the point observables on anticommuting tuples

This module carries out the anticommuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`. The Magic Square
approximate anticommutation of the variable observables is read back from the
projective dilation on which it is proved, and transported to Alice's point
observables through item 7 of `lem:qld-win-implications`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications

/-! ## Reading the dilation back on the original space -/













/-! ## The Magic Square anticommutation on the undilated strategy -/













/-! ## Reflections and the product transfer -/











/-! ## From the Magic Square variables to the point observables -/









/-! ## The anticommuting half of the twisted commutation -/

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ιL ιR : Type}
    [Fintype ιL] [DecidableEq ιL] [Fintype ιR] [DecidableEq ιR]
    (OX OZ : _root_.MIPStarRE.QPBT.PauliTuple P → _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V0 V4 : _root_.MIPStarRE.QPBT.PauliTuple P → _root_.LIDT.MIPStarRE.Quantum.Op ιR)
    (χ : EuclideanSpace ℂ (ιL × ιR)) {cd cv : ℝ}
    (hOX : ∀ ω, (OX ω)ᴴ * OX ω = 1) (hOZ : ∀ ω, (OZ ω)ᴴ * OZ ω = 1)
    (hV0 : ∀ ω, (V0 ω)ᴴ * V0 ω = 1) (hV4 : ∀ ω, (V4 ω)ᴴ * V4 ω = 1)
    (h0 : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) (fun ω => ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
          _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V0 ω)) χ‖ ^ 2) ≤ cd)
    (h4 : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) (fun ω => ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
          _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V4 ω)) χ‖ ^ 2) ≤ cd)
    (hv : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) (fun ω => ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V0 ω * V4 ω + V4 ω * V0 ω)) χ‖ ^ 2) ≤ cv) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) (fun ω => ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron (OX ω * OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) +
        _root_.MIPStarRE.QPBT.heteroKron (OZ ω * OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ‖ ^ 2) ≤
      24 * cd + 3 * cv := by
  classical
  have hpoint : ∀ ω : _root_.MIPStarRE.QPBT.PauliTuple P,
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.heteroKron (OX ω * OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) +
            _root_.MIPStarRE.QPBT.heteroKron (OZ ω * OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ‖ ^ 2 ≤
        12 * ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
            _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V0 ω)) χ‖ ^ 2 +
        12 * ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
            _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V4 ω)) χ‖ ^ 2 +
        3 * ‖_root_.MIPStarRE.QPBT.applyOperatorToState
            (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V0 ω * V4 ω + V4 ω * V0 ω)) χ‖ ^ 2 := by
    intro ω
    have h1 := _root_.MIPStarRE.QPBT.WinImplications.norm_product_transfer_le (OX ω) (OZ ω) (V0 ω) (V4 ω) χ
      (_root_.MIPStarRE.QPBT.WinImplications.heteroKron_left_isometry (OX ω) (hOX ω))
      (_root_.MIPStarRE.QPBT.WinImplications.heteroKron_right_isometry (V4 ω) (hV4 ω))
    have h2 := _root_.MIPStarRE.QPBT.WinImplications.norm_product_transfer_le (OZ ω) (OX ω) (V4 ω) (V0 ω) χ
      (_root_.MIPStarRE.QPBT.WinImplications.heteroKron_left_isometry (OZ ω) (hOZ ω))
      (_root_.MIPStarRE.QPBT.WinImplications.heteroKron_right_isometry (V0 ω) (hV0 ω))
    have hdecomp : _root_.MIPStarRE.QPBT.heteroKron (OX ω * OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) +
        _root_.MIPStarRE.QPBT.heteroKron (OZ ω * OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) =
      (_root_.MIPStarRE.QPBT.heteroKron (OX ω * OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
          _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V4 ω * V0 ω)) +
        (_root_.MIPStarRE.QPBT.heteroKron (OZ ω * OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
          _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V0 ω * V4 ω)) +
        _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V0 ω * V4 ω + V4 ω * V0 ω) := by
      rw [_root_.MIPStarRE.QPBT.heteroKron_add_right]
      abel
    set t1 : ℝ := ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
      _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V0 ω)) χ‖ with ht1
    set t2 : ℝ := ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
      _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V4 ω)) χ‖ with ht2
    set t3 : ℝ := ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V0 ω * V4 ω + V4 ω * V0 ω)) χ‖ with ht3
    set t0 : ℝ := ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (OX ω * OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) +
      _root_.MIPStarRE.QPBT.heteroKron (OZ ω * OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ‖ with ht0
    have hsum : t0 ≤
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (OX ω * OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
            _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V4 ω * V0 ω)) χ‖ +
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (OZ ω * OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
            _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V0 ω * V4 ω)) χ‖ + t3 := by
      rw [ht0, ht3, hdecomp, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_add_op,
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_add_op]
      exact le_trans (norm_add_le _ _)
        (add_le_add (norm_add_le _ _) le_rfl)
    have ht0nn : (0 : ℝ) ≤ t0 := by rw [ht0]; exact norm_nonneg _
    have ht1nn : (0 : ℝ) ≤ t1 := by rw [ht1]; exact norm_nonneg _
    have ht2nn : (0 : ℝ) ≤ t2 := by rw [ht2]; exact norm_nonneg _
    have ht3nn : (0 : ℝ) ≤ t3 := by rw [ht3]; exact norm_nonneg _
    have hbound : t0 ≤ 2 * t1 + 2 * t2 + t3 := by linarith
    have key : t0 ^ 2 ≤ 12 * t1 ^ 2 + 12 * t2 ^ 2 + 3 * t3 ^ 2 := by
      nlinarith [hbound, ht0nn, ht1nn, ht2nn, ht3nn,
        sq_nonneg (t1 - t2), sq_nonneg (2 * t1 - t3), sq_nonneg (2 * t2 - t3)]
    rw [ht0, ht1, ht2, ht3] at key
    exact key
  calc
    _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) (fun ω =>
        12 * ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
            _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V0 ω)) χ‖ ^ 2 +
        12 * ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
            _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V4 ω)) χ‖ ^ 2 +
        3 * ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V0 ω * V4 ω + V4 ω * V0 ω)) χ‖ ^ 2) :=
      _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ hpoint
    _ = 12 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) (fun ω =>
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
            _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V0 ω)) χ‖ ^ 2) +
        12 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) (fun ω =>
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
            _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (V4 ω)) χ‖ ^ 2) +
        3 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) (fun ω =>
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState
            (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL)
              (V0 ω * V4 ω + V4 ω * V0 ω)) χ‖ ^ 2) := by
      rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul, _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul,
        _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
    _ ≤ 24 * cd + 3 * cv := by linarith
