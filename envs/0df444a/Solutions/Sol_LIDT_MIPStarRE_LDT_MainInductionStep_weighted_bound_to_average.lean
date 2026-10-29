-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MainInductionStep.weighted_bound_to_average
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:44:02.272509+00:00
-- url     : https://prove2.me/submissions/59703505-dcdd-4fae-b40c-5652610f3551

-- Generated proof for MIPStarRE.LDT.MainInductionStep.weighted_bound_to_average.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Lean.Elab.Tactic
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

end LIDT

open LIDT
/-!
# Section 6 -- Restricted Probability Common Lemmas

This module contains the averaging and scalar normalization lemmas shared by the
axis-parallel, diagonal, and answer-valued restricted-probability bounds.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    {a b : _root_.LIDT.MIPStarRE.LDT.Error}
    (h : _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params * a ≤ b) :
    a ≤ _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceConditioningLoss params * b := by
  have hmul :
      _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceConditioningLoss params * (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params * a) ≤
        _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceConditioningLoss params * b :=
    mul_le_mul_of_nonneg_left h (by
      unfold _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceConditioningLoss
      positivity)
  have hcancel :
      _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceConditioningLoss params * (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params * a) = a := by
    unfold _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceConditioningLoss _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight
    have hm : (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt params.hm)
    have hms : (((params.m + 1 : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error)) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero params.m)
    field_simp [hm, hms]
  calc
    a = _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceConditioningLoss params * (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params * a) := by
          symm
          exact hcancel
    _ ≤ _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceConditioningLoss params * b := hmul
