-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MainInductionStep.weighted_embedded_average_le_full_average
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:44:02.500326+00:00
-- url     : https://prove2.me/submissions/25e72c73-08b0-4bf0-a394-7a28ab49d2c0

-- Generated proof for MIPStarRE.LDT.MainInductionStep.weighted_embedded_average_le_full_average.
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
    (f : Fin params.next.m → _root_.LIDT.MIPStarRE.LDT.Error)
    (hf : ∀ i, 0 ≤ f i) :
    _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params *
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin params.m)) (fun i => f (_root_.LIDT.MIPStarRE.LDT.embedCoord params i)) ≤
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin params.next.m)) f := by
  have hm : (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hm)
  have hnextm : (params.next.m : _root_.LIDT.MIPStarRE.LDT.Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.next.hm)
  have hsum_le :
      ∑ i : Fin params.m, f (_root_.LIDT.MIPStarRE.LDT.embedCoord params i) ≤ ∑ j : Fin params.next.m, f j := by
    classical
    calc
      ∑ i : Fin params.m, f (_root_.LIDT.MIPStarRE.LDT.embedCoord params i)
        = Finset.sum
            (((Finset.univ : Finset (Fin params.m)).image (_root_.LIDT.MIPStarRE.LDT.embedCoord params)))
            (fun j => f j) := by
            symm
            refine Finset.sum_image ?_
            intro a _ b _ hab
            exact _root_.LIDT.MIPStarRE.LDT.embedCoord_injective params hab
      _ ≤ ∑ j : Fin params.next.m, f j := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (by simp) ?_
            intro j _ _
            exact hf j
  calc
    _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params *
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin params.m)) (fun i => f (_root_.LIDT.MIPStarRE.LDT.embedCoord params i))
      = _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params *
          ∑ i : Fin params.m, (1 / (params.m : _root_.LIDT.MIPStarRE.LDT.Error)) * f (_root_.LIDT.MIPStarRE.LDT.embedCoord params i) := by
            simp [_root_.LIDT.MIPStarRE.LDT.avgOver, _root_.LIDT.MIPStarRE.LDT.uniformDistribution, Fintype.card_fin]
    _ = ∑ i : Fin params.m,
          (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params * (1 / (params.m : _root_.LIDT.MIPStarRE.LDT.Error)))
              * f (_root_.LIDT.MIPStarRE.LDT.embedCoord params i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
    _ = ∑ i : Fin params.m, (1 / (params.next.m : _root_.LIDT.MIPStarRE.LDT.Error)) * f (_root_.LIDT.MIPStarRE.LDT.embedCoord params i) := by
            have hnext : (params.next.m : _root_.LIDT.MIPStarRE.LDT.Error) = (params.m : _root_.LIDT.MIPStarRE.LDT.Error) + 1 := by
              simp
            have hplus_ne : (params.m : _root_.LIDT.MIPStarRE.LDT.Error) + 1 ≠ 0 := hnext ▸ hnextm
            have hweight :
                _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params =
                  (params.m : _root_.LIDT.MIPStarRE.LDT.Error) / ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) + 1) := by
              unfold _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight
              push_cast
              ring
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hweight, hnext]
            field_simp
    _ = (1 / (params.next.m : _root_.LIDT.MIPStarRE.LDT.Error)) * ∑ i : Fin params.m, f (_root_.LIDT.MIPStarRE.LDT.embedCoord params i) := by
            symm
            rw [Finset.mul_sum]
    _ ≤ (1 / (params.next.m : _root_.LIDT.MIPStarRE.LDT.Error)) * ∑ j : Fin params.next.m, f j := by
            exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = ∑ j : Fin params.next.m, (1 / (params.next.m : _root_.LIDT.MIPStarRE.LDT.Error)) * f j := by
            rw [Finset.mul_sum]
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin params.next.m)) f := by
            simp [_root_.LIDT.MIPStarRE.LDT.avgOver, _root_.LIDT.MIPStarRE.LDT.uniformDistribution, Fintype.card_fin]
