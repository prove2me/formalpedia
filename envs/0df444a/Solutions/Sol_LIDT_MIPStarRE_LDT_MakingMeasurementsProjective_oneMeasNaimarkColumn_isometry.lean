-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn_isometry
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:06:22.491672+00:00
-- url     : https://prove2.me/submissions/4e8867b4-32ef-49dd-beac-e71dd7ab0285

-- Generated proof for MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn_isometry.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkCore
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/MakingMeasurementsProjective/NaimarkCore.lean. -/
/-!
# Section 5 — Naimark core

Core projector and compression lemmas for the one-measurement Naimark
dilation construction.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT
open MIPStarRE.Quantum

/-! ### One-measurement Naimark (Lemma 5.2) -/





















/-- The one-measurement Naimark slack operator is positive semidefinite. -/
lemma oneMeasNaimarkRemainder_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) :
    0 ≤ oneMeasNaimarkRemainder M := by
  exact sub_nonneg.mpr M.sum_le_one










end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT

open LIDT
/-!
# Section 5 — Naimark core

Core projector and compression lemmas for the one-measurement Naimark
dilation construction.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT
open MIPStarRE.Quantum

/-! ### One-measurement Naimark (Lemma 5.2) -/

theorem solution
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : _root_.LIDT.MIPStarRE.Quantum.Submeasurement α d) :
    (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M)ᴴ * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M =
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj (α := α) (d := d) := by
  classical
  ext x y
  rcases x with ⟨i, ox⟩
  rcases y with ⟨j, oy⟩
  cases ox <;> cases oy
  · rw [Matrix.mul_apply]
    rw [show ∑ z : d × Option α,
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M)ᴴ (i, none) z * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M z (j, none) =
          ∑ k : d, ∑ o : Option α,
            (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M)ᴴ (i, none) (k, o) *
              _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M (k, o) (j, none) by
        simpa using
          (Fintype.sum_prod_type
            (f := fun z : d × Option α =>
              (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M)ᴴ (i, none) z *
                _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M z (j, none)))]
    simp_rw [Fintype.sum_option]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    have hR :
        (CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkRemainder M))ᴴ =
          CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkRemainder M) := by
      simpa using (CFC.sqrt_nonneg (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkRemainder M)).isHermitian.eq
    have hMa : ∀ a : α, (CFC.sqrt (M.effect a))ᴴ = CFC.sqrt (M.effect a) := by
      intro a
      simpa using (CFC.sqrt_nonneg (M.effect a)).isHermitian.eq
    have hR_sq :
        CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkRemainder M) * CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkRemainder M) =
          _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkRemainder M := by
      simpa using CFC.sqrt_mul_sqrt_self (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkRemainder M)
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkRemainder_nonneg M)
    have hMa_sq : ∀ a : α,
        CFC.sqrt (M.effect a) * CFC.sqrt (M.effect a) = M.effect a := by
      intro a
      simpa using CFC.sqrt_mul_sqrt_self (M.effect a) (M.pos a)
    calc
      ∑ k : d,
          star ((_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M) (k, none) (i, none)) *
            (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M) (k, none) (j, none)
        + ∑ a : α, ∑ k : d,
            star ((_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M) (k, some a) (i, none)) *
              (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M) (k, some a) (j, none)
          = (((CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkRemainder M))ᴴ *
                CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkRemainder M)) i j) +
              ∑ a : α, (((CFC.sqrt (M.effect a))ᴴ * CFC.sqrt (M.effect a)) i j) := by
              simp [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn, Matrix.mul_apply]
      _ = ((CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkRemainder M) *
              CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkRemainder M)) i j) +
            ∑ a : α, ((CFC.sqrt (M.effect a) * CFC.sqrt (M.effect a)) i j) := by
            simp [hR, hMa]
      _ = (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkRemainder M) i j + ∑ a : α, (M.effect a) i j := by
            simp [hR_sq, hMa_sq]
      _ = (1 : _root_.LIDT.MIPStarRE.Quantum.Op d) i j := by
            simp [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkRemainder, Matrix.sub_apply, Matrix.sum_apply,
              sub_eq_add_neg, add_comm]
      _ = (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj (α := α) (d := d)) (i, none) (j, none) := by
            simp [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkAuxTransition, Matrix.kronecker]
  · simp [Matrix.mul_apply, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj,
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkAuxTransition, Matrix.kronecker]
  · simp [Matrix.mul_apply, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj,
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkAuxTransition, Matrix.kronecker]
  · simp [Matrix.mul_apply, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj,
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkAuxTransition, Matrix.kronecker]
