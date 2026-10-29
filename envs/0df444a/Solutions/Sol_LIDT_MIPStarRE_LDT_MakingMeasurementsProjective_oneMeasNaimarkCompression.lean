-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkCompression
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:06:22.720573+00:00
-- url     : https://prove2.me/submissions/95f15d52-e1f8-4851-9d69-0b8a53bc6e42

-- Generated proof for MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkCompression.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_isProj_kronecker
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_oneMeasNaimarkOutcomeProj_mul_column

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

/-- The rank-one projector onto an `Option` basis vector is projective. -/
lemma optionBasisProj_isProj {α : Type*} [Fintype α] [DecidableEq α]
    (oa : Option α) :
    MIPStarRE.Quantum.IsProj
      (Matrix.single oa oa (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) := by
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · exact isIdempotentElem_iff.mpr (by simp)
  · exact (Matrix.IsHermitian.ext fun i j => by
      by_cases hio : oa = i <;> by_cases hjo : oa = j <;>
        simp [Matrix.single, hio, hjo, and_comm]).isSelfAdjoint






























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
    (M : _root_.LIDT.MIPStarRE.Quantum.Submeasurement α d) (a : α) :
    (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M)ᴴ *
        _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) *
        _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M =
      Matrix.kronecker (M.effect a) (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α) := by
  let P : _root_.LIDT.MIPStarRE.Quantum.Op (d × Option α) :=
    _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a)
  have hP_proj : _root_.LIDT.MIPStarRE.Quantum.IsProj P := by
    dsimp [P, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj]
    exact _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.isProj_kronecker
      ((IsStarProjection.one _))
      (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.optionBasisProj_isProj (α := α) (some a))
  have hsqrt : (CFC.sqrt (M.effect a))ᴴ = CFC.sqrt (M.effect a) := by
    simpa using (CFC.sqrt_nonneg (M.effect a)).isHermitian.eq
  have hsingle :
      (Matrix.single (some a) none (1 : ℂ))ᴴ * Matrix.single (some a) none (1 : ℂ) =
        _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α := by
    ext x y
    cases x <;> cases y <;>
      simp [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector, Matrix.mul_apply, Matrix.single_apply]
  calc
    (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M)ᴴ * P * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M
        = (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M)ᴴ * (P * P) * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M := by
            rw [hP_proj.isIdempotentElem.eq]
    _ = (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M)ᴴ * Pᴴ * (P * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M) := by
          rw [hP_proj.isSelfAdjoint.isHermitian.eq]
          simp [mul_assoc]
    _ = (P * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M)ᴴ * (P * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M) := by
          simp [Matrix.conjTranspose_mul, mul_assoc]
    _ =
        (Matrix.kronecker (CFC.sqrt (M.effect a)) (Matrix.single (some a) none (1 : ℂ)))ᴴ *
          Matrix.kronecker (CFC.sqrt (M.effect a)) (Matrix.single (some a) none (1 : ℂ)) := by
            rw [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj_mul_column]
    _ =
        Matrix.kronecker ((CFC.sqrt (M.effect a))ᴴ * CFC.sqrt (M.effect a))
          ((Matrix.single (some a) none (1 : ℂ))ᴴ * Matrix.single (some a) none (1 : ℂ)) := by
            simpa [Matrix.conjTranspose_kronecker] using
              (Matrix.mul_kronecker_mul
                ((CFC.sqrt (M.effect a))ᴴ) (CFC.sqrt (M.effect a))
                ((Matrix.single (some a) none (1 : ℂ))ᴴ)
                (Matrix.single (some a) none (1 : ℂ))).symm
    _ = Matrix.kronecker (M.effect a) (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α) := by
          rw [hsingle]
          simp [hsqrt, CFC.sqrt_mul_sqrt_self, M.pos a]
