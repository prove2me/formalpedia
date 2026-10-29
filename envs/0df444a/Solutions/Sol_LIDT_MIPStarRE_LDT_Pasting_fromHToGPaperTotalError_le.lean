-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToGPaperTotalError_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:29:29.340495+00:00
-- url     : https://prove2.me/submissions/f3deccaa-289f-4744-b46f-57a69cdd0a58

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToGPaperTotalError_le.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_BernoulliTail
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
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
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian
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

end LIDT

open LIDT
/-!
# Section 12 pasting: exact identities and error-bound lemma

Exact recurrence identities and the paper-total error absorption lemma that
assemble the final `fromHToG` telescope conclusion.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





-- Keep the final product rearrangement explicit; asking `nlinarith` to find it
-- was the only part of this scalar absorption proof that needed extra heartbeats.

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error) (k : ℕ)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta_le_one : zeta ≤ 1) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPaperTotalError params gamma zeta k ≤
      _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGError params gamma zeta k := by
  have hm_nonneg : 0 ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by positivity
  have hm_ge_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hk_nonneg : 0 ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) := by positivity
  have hratio_nonneg : 0 ≤ ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    positivity
  let sixteenthSum : _root_.LIDT.MIPStarRE.LDT.Error :=
    Real.rpow gamma (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) +
      Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) +
      Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error))
  let thirtysecondSum : _root_.LIDT.MIPStarRE.LDT.Error :=
    Real.rpow gamma (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) +
      Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) +
      Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))
  have hgamma32_nonneg : 0 ≤ Real.rpow gamma (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
    Real.rpow_nonneg hgamma_nonneg _
  have hzeta32_nonneg : 0 ≤ Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
    Real.rpow_nonneg hzeta_nonneg _
  have hratio32_nonneg :
      0 ≤ Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
    Real.rpow_nonneg hratio_nonneg _
  have hthirtysecond_nonneg : 0 ≤ thirtysecondSum := by
    dsimp [thirtysecondSum]
    positivity
  have hsixteenth_nonneg : 0 ≤ sixteenthSum := by
    dsimp [sixteenthSum]
    positivity
  have hgamma32_sq :
      (Real.rpow gamma (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ) =
        Real.rpow gamma (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    calc
      (Real.rpow gamma (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ)
          = (Real.rpow gamma (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : _root_.LIDT.MIPStarRE.LDT.Error) := by norm_num
      _ = Real.rpow gamma ((1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) * (2 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            symm
            exact Real.rpow_mul hgamma_nonneg _ _
      _ = Real.rpow gamma (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by norm_num
  have hzeta32_sq :
      (Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ) =
        Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    calc
      (Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ)
          = (Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : _root_.LIDT.MIPStarRE.LDT.Error) := by norm_num
      _ = Real.rpow zeta ((1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) * (2 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            symm
            exact Real.rpow_mul hzeta_nonneg _ _
      _ = Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by norm_num
  have hratio32_sq :
      (Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ) =
        Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    calc
      (Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))) ^
          (2 : ℕ)
          = (Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))) ^
              (2 : _root_.LIDT.MIPStarRE.LDT.Error) := by norm_num
      _ = Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)))
            ((1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) * (2 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            symm
            exact Real.rpow_mul hratio_nonneg _ _
      _ = Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            norm_num
  have hsixteenth_le_thirtysecond_sq : sixteenthSum ≤ thirtysecondSum ^ (2 : ℕ) := by
    let a : _root_.LIDT.MIPStarRE.LDT.Error := Real.rpow gamma (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))
    let b : _root_.LIDT.MIPStarRE.LDT.Error := Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))
    let c : _root_.LIDT.MIPStarRE.LDT.Error := Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))
    have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
    have hb_nonneg : 0 ≤ b := by dsimp [b]; positivity
    have hc_nonneg : 0 ≤ c := by dsimp [c]; positivity
    have hsq : a ^ (2 : ℕ) + b ^ (2 : ℕ) + c ^ (2 : ℕ) ≤ (a + b + c) ^ (2 : ℕ) := by
      nlinarith [ha_nonneg, hb_nonneg, hc_nonneg]
    rw [hgamma32_sq, hzeta32_sq, hratio32_sq] at hsq
    simpa [a, b, c, sixteenthSum, thirtysecondSum] using hsq
  have hzeta_le_sixteenth : zeta ≤ Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    have hpow : (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ (1 : _root_.LIDT.MIPStarRE.LDT.Error) := by norm_num
    simpa using Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta_le_one (by norm_num) hpow
  have hsqrt_two_zeta :
      Real.sqrt (2 * zeta) ≤ 2 * Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    have hzeta16_nonneg : 0 ≤ Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
      Real.rpow_nonneg hzeta_nonneg _
    have hzeta32_sq' :
        (Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ) =
          Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := hzeta32_sq
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · positivity
    · calc
        2 * zeta ≤ 4 * Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
          nlinarith [hzeta_le_sixteenth, hzeta16_nonneg]
        _ = (2 * Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ) := by
          rw [mul_pow, hzeta32_sq']
          norm_num
  have hzeta32_le_sum : Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ thirtysecondSum := by
    have htail : 0 ≤ Real.rpow gamma (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) +
        Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
      exact add_nonneg hgamma32_nonneg hratio32_nonneg
    dsimp [thirtysecondSum]
    rw [show gamma ^ (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) + zeta ^ (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) +
        (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) =
        zeta ^ (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) +
          (gamma ^ (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) +
            (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))) by ring]
    exact (le_add_of_nonneg_right htail :
      Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) +
        (Real.rpow gamma (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) +
          Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))))
  have hfirst :
      (k : _root_.LIDT.MIPStarRE.LDT.Error) * (2 * Real.sqrt (2 * zeta)) ≤
        4 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * thirtysecondSum := by
    calc
      (k : _root_.LIDT.MIPStarRE.LDT.Error) * (2 * Real.sqrt (2 * zeta))
          ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) * (2 * (2 * Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)))) := by
            gcongr
      _ = 4 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) := by ring
      _ ≤ 4 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) * thirtysecondSum) := by
            have hzeta32_le_msum :
                Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
                  (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * thirtysecondSum := by
              calc
                Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ thirtysecondSum := hzeta32_le_sum
                _ = 1 * thirtysecondSum := by ring
                _ ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * thirtysecondSum := by
                      exact mul_le_mul_of_nonneg_right hm_ge_one hthirtysecond_nonneg
            gcongr
      _ = 4 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * thirtysecondSum := by ring
  have hcomm_sqrt :
      Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k) ≤
        21 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * thirtysecondSum := by
    have hright_nonneg : 0 ≤ 21 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * thirtysecondSum := by
      positivity
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · exact hright_nonneg
    · have hm_sq_ge : (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ) := by
        nlinarith [hm_ge_one]
      calc
        _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k
            = 426 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * sixteenthSum := by
              simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError, sixteenthSum]
        _ ≤ 441 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) *
              (thirtysecondSum ^ (2 : ℕ)) := by
              gcongr
              norm_num
        _ ≤ 441 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
              (thirtysecondSum ^ (2 : ℕ)) := by
              gcongr
        _ = (21 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * thirtysecondSum) ^ (2 : ℕ) := by
              ring
  have hsecond :
      2 * Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k) ≤
        42 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * thirtysecondSum := by
    nlinarith [hcomm_sqrt]
  by_cases hk0 : k = 0
  · subst k
    simp [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPaperTotalError, _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceError, _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGError]
  have hk_ge_one_nat : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
  have hk_ge_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) := by exact_mod_cast hk_ge_one_nat
  have hk_le_sq : (k : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ) := by nlinarith
  have hfirst_quad :
      (k : _root_.LIDT.MIPStarRE.LDT.Error) * (2 * Real.sqrt (2 * zeta)) ≤
        4 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * thirtysecondSum := by
    have hmul :
        4 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * thirtysecondSum ≤
          4 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * thirtysecondSum := by
      have hcoeff_nonneg : 0 ≤ 4 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * thirtysecondSum := by positivity
      have hmul' := mul_le_mul_of_nonneg_left hk_le_sq hcoeff_nonneg
      nlinarith
    exact le_trans hfirst hmul
  have hsecond_quad :
      (k : _root_.LIDT.MIPStarRE.LDT.Error) * (2 * Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k)) ≤
        42 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * thirtysecondSum := by
    have hmul := mul_le_mul_of_nonneg_left hsecond hk_nonneg
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
  calc
    _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPaperTotalError params gamma zeta k
        = (k : _root_.LIDT.MIPStarRE.LDT.Error) * (2 * Real.sqrt (2 * zeta)) +
            (k : _root_.LIDT.MIPStarRE.LDT.Error) * (2 * Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k)) := by
          simp [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGPaperTotalError, _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGRecurrenceError, Real.sqrt_eq_rpow]
          ring
    _ ≤ 4 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * thirtysecondSum +
          42 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * thirtysecondSum := by
          exact add_le_add hfirst_quad hsecond_quad
    _ = _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGError params gamma zeta k := by
          simp [_root_.LIDT.MIPStarRE.LDT.Pasting.fromHToGError, thirtysecondSum]
          ring
