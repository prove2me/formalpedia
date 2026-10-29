-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.isProj_unitary_conj
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:53:11.227145+00:00
-- url     : https://prove2.me/submissions/2773054a-6b70-479b-a2d5-15277125dce4

-- Generated proof for MIPStarRE.LDT.MakingMeasurementsProjective.isProj_unitary_conj.
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

theorem solution {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) {P : _root_.LIDT.MIPStarRE.Quantum.Op n}
    (hP : _root_.LIDT.MIPStarRE.Quantum.IsProj P) :
    _root_.LIDT.MIPStarRE.Quantum.IsProj
      (((U : _root_.LIDT.MIPStarRE.Quantum.Op n)ᴴ) * P * (U : _root_.LIDT.MIPStarRE.Quantum.Op n)) := by
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · calc
      (((U : _root_.LIDT.MIPStarRE.Quantum.Op n)ᴴ) * P * (U : _root_.LIDT.MIPStarRE.Quantum.Op n)) *
      (((U : _root_.LIDT.MIPStarRE.Quantum.Op n)ᴴ) * P * (U : _root_.LIDT.MIPStarRE.Quantum.Op n))
          = (U : _root_.LIDT.MIPStarRE.Quantum.Op n)ᴴ * P * ((U : _root_.LIDT.MIPStarRE.Quantum.Op n) *
              (U : _root_.LIDT.MIPStarRE.Quantum.Op n)ᴴ) * P * (U : _root_.LIDT.MIPStarRE.Quantum.Op n) := by
                simp [mul_assoc]
      _ = (U : _root_.LIDT.MIPStarRE.Quantum.Op n)ᴴ * P * 1 * P * (U : _root_.LIDT.MIPStarRE.Quantum.Op n) := by
            have hUU' : (U : _root_.LIDT.MIPStarRE.Quantum.Op n) * (U : _root_.LIDT.MIPStarRE.Quantum.Op n)ᴴ = 1 := by
              change
                (U : _root_.LIDT.MIPStarRE.Quantum.Op n) *
                  ((star U : Matrix.unitaryGroup n ℂ) : _root_.LIDT.MIPStarRE.Quantum.Op n) = 1
              exact Unitary.coe_mul_star_self U
            rw [hUU']
      _ = (U : _root_.LIDT.MIPStarRE.Quantum.Op n)ᴴ * (P * P) * (U : _root_.LIDT.MIPStarRE.Quantum.Op n) := by
            simp [mul_assoc]
      _ = (U : _root_.LIDT.MIPStarRE.Quantum.Op n)ᴴ * P * (U : _root_.LIDT.MIPStarRE.Quantum.Op n) := by
            rw [hP.isIdempotentElem.eq]
  · calc
      ((((U : _root_.LIDT.MIPStarRE.Quantum.Op n)ᴴ) * P * (U : _root_.LIDT.MIPStarRE.Quantum.Op n)))ᴴ
          = (U : _root_.LIDT.MIPStarRE.Quantum.Op n)ᴴ * Pᴴ * (U : _root_.LIDT.MIPStarRE.Quantum.Op n) := by
              simp [mul_assoc]
      _ = (U : _root_.LIDT.MIPStarRE.Quantum.Op n)ᴴ * P * (U : _root_.LIDT.MIPStarRE.Quantum.Op n) := by
            rw [hP.isSelfAdjoint.isHermitian.eq]
