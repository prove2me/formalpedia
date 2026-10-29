-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj_mul_column
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:53:11.029512+00:00
-- url     : https://prove2.me/submissions/85294bd4-e8b5-406b-acb0-bf0578b49307

-- Generated proof for MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj_mul_column.
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

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

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
    (M : _root_.LIDT.MIPStarRE.Quantum.Submeasurement α d) (a : α) :
    _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M =
      Matrix.kronecker (CFC.sqrt (M.effect a)) (Matrix.single (some a) none (1 : ℂ)) := by
  ext x y
  rcases x with ⟨i, ox⟩
  rcases y with ⟨j, oy⟩
  rcases ox with _ | a'
  · rcases oy with _ | b
    · rw [Matrix.mul_apply]
      rw [show ∑ z : d × Option α,
          _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, none) z *
              _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M z (j, none) =
            ∑ k : d, ∑ o : Option α,
              _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, none) (k, o) *
                _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M (k, o) (j, none) by
        simpa using
          (Fintype.sum_prod_type
            (f := fun z : d × Option α =>
              _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, none) z *
                _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M z (j, none)))]
      simp [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkAuxTransition,
        Matrix.kronecker]
    · rw [Matrix.mul_apply]
      rw [show ∑ z : d × Option α,
          _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, none) z *
              _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M z (j, some b) =
            ∑ k : d, ∑ o : Option α,
              _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, none) (k, o) *
                _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M (k, o) (j, some b) by
        simpa using
          (Fintype.sum_prod_type
            (f := fun z : d × Option α =>
              _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, none) z *
                _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M z (j, some b)))]
      simp [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkAuxTransition,
        Matrix.kronecker]
  · rcases oy with _ | b
    · rw [Matrix.mul_apply]
      rw [show ∑ z : d × Option α,
          _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, some a') z *
              _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M z (j, none) =
            ∑ k : d, ∑ o : Option α,
              _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, some a') (k, o) *
                _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M (k, o) (j, none) by
        simpa using
          (Fintype.sum_prod_type
            (f := fun z : d × Option α =>
              _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, some a') z *
                _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M z (j, none)))]
      by_cases h : a' = a
      · subst a'
        simp only [Fintype.sum_option, Matrix.kronecker, Matrix.kroneckerMap_apply,
          Matrix.single_apply_same, mul_one, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj,
          _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkAuxTransition, Matrix.one_apply]
        rw [Finset.sum_eq_single i]
        · rw [Finset.sum_eq_single a]
          · simp
          · intro x _ hxa
            have hax : a ≠ x := fun h => hxa h.symm
            simp [hax]
          · simp
        · intro x _ hxi
          have hix : i ≠ x := fun h => hxi h.symm
          simp [hix]
        · simp
      · simp [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkAuxTransition,
          Matrix.kronecker, show a ≠ a' by exact fun h' => h h'.symm]
    · rw [Matrix.mul_apply]
      rw [show ∑ z : d × Option α,
          _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, some a') z *
              _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M z (j, some b) =
            ∑ k : d, ∑ o : Option α,
              _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, some a') (k, o) *
                _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M (k, o) (j, some b) by
        simpa using
          (Fintype.sum_prod_type
            (f := fun z : d × Option α =>
              _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, some a') z *
                _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M z (j, some b)))]
      simp [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkAuxTransition,
        Matrix.kronecker]
