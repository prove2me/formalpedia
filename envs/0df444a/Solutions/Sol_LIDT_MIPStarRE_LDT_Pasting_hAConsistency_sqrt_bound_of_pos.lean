-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.hAConsistency_sqrt_bound_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:01:56.496765+00:00
-- url     : https://prove2.me/submissions/259ed496-778b-4b2a-9555-b4c968929847

-- Generated proof for MIPStarRE.LDT.Pasting.hAConsistency_sqrt_bound_of_pos.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_ScalarTerms
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
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
import Mathlib
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/Common.lean. -/
/-!
# Section 12 pasting: comparison common helpers

Shared postprocessing, symmetry, distribution, boundedness, and arithmetic helpers for the Section
12 comparison lemmas.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

















lemma sqrt_min_le_rpow32
    (x : Error) (hx : 0 ≤ x) :
    Real.sqrt (min x 1) ≤ Real.rpow x (1 / (32 : Error)) := by
  have hmin_nonneg : 0 ≤ min x 1 := by positivity
  have hmin_le_one : min x 1 ≤ 1 := min_le_right _ _
  calc
    Real.sqrt (min x 1) = (min x 1) ^ (1 / (2 : Error)) := by
          rw [Real.sqrt_eq_rpow]
    _ ≤ (min x 1) ^ (1 / (32 : Error)) := by
          exact Real.rpow_le_rpow_of_exponent_ge'
            hmin_nonneg hmin_le_one (by norm_num) (by norm_num)
    _ ≤ x ^ (1 / (32 : Error)) := by
          exact Real.rpow_le_rpow hmin_nonneg (min_le_left _ _) (by positivity)





end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: comparison common helpers

Shared postprocessing, symmetry, distribution, boundedness, and arithmetic helpers for the Section
12 comparison lemmas.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    (eps delta : _root_.LIDT.MIPStarRE.LDT.Error)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta) :
    Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * min eps 1 + 4 * min delta 1)
      ≤ 3 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) *
          (Real.rpow eps (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) + Real.rpow delta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))) := by
  have hm_nonneg : 0 ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by positivity
  have hm_ge_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hk_sq_ge_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ) := by
    have hk_ge_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) := by exact_mod_cast hk_pos
    nlinarith
  have hsqrt_m_le : Real.sqrt (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · exact hm_nonneg
    · nlinarith
  have hsqrt8_le_three : Real.sqrt (8 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 3 := by
    have : (Real.sqrt (8 : _root_.LIDT.MIPStarRE.LDT.Error)) ^ (2 : ℕ) ≤ (3 : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ) := by
      norm_num
    nlinarith [Real.sq_sqrt (show 0 ≤ (8 : _root_.LIDT.MIPStarRE.LDT.Error) by positivity), this]
  have heps_term :
      Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * min eps 1)
        ≤ 3 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) *
            Real.rpow eps (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    calc
      Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * min eps 1)
        = Real.sqrt (8 : _root_.LIDT.MIPStarRE.LDT.Error) * Real.sqrt (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Real.sqrt (min eps 1) := by
            rw [show 8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * min eps 1 =
                (8 : _root_.LIDT.MIPStarRE.LDT.Error) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) * min eps 1) by
              ring]
            rw [Real.sqrt_mul (show 0 ≤ (8 : _root_.LIDT.MIPStarRE.LDT.Error) by positivity)]
            rw [Real.sqrt_mul hm_nonneg (min eps 1)]
            ring
      _ ≤ 3 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Real.rpow eps (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            have hfac :
                Real.sqrt (8 : _root_.LIDT.MIPStarRE.LDT.Error) * Real.sqrt (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ≤
                  3 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
              calc
                Real.sqrt (8 : _root_.LIDT.MIPStarRE.LDT.Error) * Real.sqrt (params.m : _root_.LIDT.MIPStarRE.LDT.Error)
                  ≤ 3 * Real.sqrt (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
                      exact mul_le_mul_of_nonneg_right hsqrt8_le_three (by positivity)
                _ ≤ 3 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
                      exact mul_le_mul_of_nonneg_left hsqrt_m_le (by positivity)
            have hmin : Real.sqrt (min eps 1) ≤ Real.rpow eps (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
              _root_.LIDT.MIPStarRE.LDT.Pasting.sqrt_min_le_rpow32 eps heps_nonneg
            have hright_nonneg : 0 ≤ Real.rpow eps (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
              Real.rpow_nonneg heps_nonneg _
            have hsqrt_nonneg : 0 ≤ Real.sqrt (min eps 1) := by positivity
            calc
              Real.sqrt (8 : _root_.LIDT.MIPStarRE.LDT.Error) * Real.sqrt (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Real.sqrt (min eps 1)
                ≤ (3 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error)) * Real.sqrt (min eps 1) := by
                    exact mul_le_mul_of_nonneg_right hfac hsqrt_nonneg
              _ ≤ (3 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error)) * Real.rpow eps (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
                    exact mul_le_mul_of_nonneg_left hmin (by positivity)
      _ ≤ 3 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) *
            Real.rpow eps (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            have hroot_nonneg : 0 ≤ Real.rpow eps (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
              Real.rpow_nonneg heps_nonneg _
            have hmroot_nonneg :
                0 ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Real.rpow eps (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
              positivity
            nlinarith
  have hdelta_term :
      Real.sqrt (4 * min delta 1)
        ≤ 3 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) *
            Real.rpow delta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    calc
      Real.sqrt (4 * min delta 1)
        = 2 * Real.sqrt (min delta 1) := by
            rw [show 4 * min delta 1 = (4 : _root_.LIDT.MIPStarRE.LDT.Error) * (min delta 1) by ring]
            rw [Real.sqrt_mul (show 0 ≤ (4 : _root_.LIDT.MIPStarRE.LDT.Error) by positivity) (min delta 1)]
            norm_num
      _ ≤ 2 * Real.rpow delta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            have hmin : Real.sqrt (min delta 1) ≤ Real.rpow delta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
              _root_.LIDT.MIPStarRE.LDT.Pasting.sqrt_min_le_rpow32 delta hdelta_nonneg
            nlinarith
      _ ≤ 3 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) *
            Real.rpow delta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            have hroot_nonneg : 0 ≤ Real.rpow delta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
              Real.rpow_nonneg hdelta_nonneg _
            have hmroot_nonneg :
                0 ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Real.rpow delta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
              positivity
            nlinarith [hk_sq_ge_one, hm_ge_one, hmroot_nonneg]
  have hsqrt_add :
      Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * min eps 1 + 4 * min delta 1)
        ≤ Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * min eps 1) + Real.sqrt (4 * min delta 1) := by
    have ha : 0 ≤ 8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * min eps 1 := by positivity
    have hb : 0 ≤ 4 * min delta 1 := by positivity
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · positivity
    · have hcross :
          0 ≤ 2 * Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * min eps 1) *
            Real.sqrt (4 * min delta 1) := by
          positivity
      nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, hcross]
  calc
    Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * min eps 1 + 4 * min delta 1)
      ≤ Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * min eps 1) + Real.sqrt (4 * min delta 1) := hsqrt_add
    _ ≤ 3 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) *
          Real.rpow eps (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) +
          3 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) *
            Real.rpow delta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            exact add_le_add heps_term hdelta_term
    _ = 3 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) *
          (Real.rpow eps (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) + Real.rpow delta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))) := by
            ring
