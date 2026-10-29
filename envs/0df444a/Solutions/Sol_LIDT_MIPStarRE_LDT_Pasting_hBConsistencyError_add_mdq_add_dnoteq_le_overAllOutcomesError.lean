-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.hBConsistencyError_add_mdq_add_dnoteq_le_overAllOutcomesError
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:40:01.443201+00:00
-- url     : https://prove2.me/submissions/61692916-e86b-4a1c-910a-0809e449ba94

-- Generated proof for MIPStarRE.LDT.Pasting.hBConsistencyError_add_mdq_add_dnoteq_le_overAllOutcomesError.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_BackChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Chain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_FlatChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_PrefixMoved
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadMass
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Core_LdGbcon
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
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

end LIDT

open LIDT
/-!
# Section 12 pasting: over all outcomes — error terms and eligible mass

Error-arithmetic lemmas, eligible-mass bounds, and mass identities that feed the final
`lem:over-all-outcomes` comparison.

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
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (eps delta gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error) (k : ℕ)
    (hd : 0 < params.d)
    (hdq_le : params.d ≤ params.q)
    (hkEligible : params.d + 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.hBConsistencyError params eps delta gamma zeta k +
        ((params.m * params.d : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) +
        ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) ≤
      _root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesError params eps delta gamma zeta k := by
  let ratio : _root_.LIDT.MIPStarRE.LDT.Error := (params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)
  let R : _root_.LIDT.MIPStarRE.LDT.Error := Real.rpow ratio (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))
  let S : _root_.LIDT.MIPStarRE.LDT.Error :=
    Real.rpow eps (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) +
      Real.rpow delta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) +
      Real.rpow gamma (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) +
      Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) + R
  have hq_pos : 0 < (params.q : _root_.LIDT.MIPStarRE.LDT.Error) := by exact_mod_cast params.hq
  have hd_ge_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (params.d : _root_.LIDT.MIPStarRE.LDT.Error) := by exact_mod_cast hd
  have hm_ge_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hk_ge_one_nat : 1 ≤ k := by omega
  have hk_ge_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) := by exact_mod_cast hk_ge_one_nat
  have hk2_ge_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ) := by
    nlinarith [mul_le_mul hk_ge_one hk_ge_one (by positivity : (0 : Error) ≤ 1)
      (by positivity : (0 : Error) ≤ (k : Error))]
  have hratio_nonneg : 0 ≤ ratio := by positivity
  have hratio_le_one : ratio ≤ 1 := by
    dsimp [ratio]
    rw [div_le_iff₀ hq_pos]
    norm_num
    exact_mod_cast hdq_le
  have hratio_le_R : ratio ≤ R := by
    simpa [R, Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' hratio_nonneg hratio_le_one
        (by norm_num : 0 ≤ (1 / (32 : Error)))
        (by norm_num : (1 / (32 : Error)) ≤ (1 : Error)))
  have hR_nonneg : 0 ≤ R := Real.rpow_nonneg hratio_nonneg _
  have hR_le_S : R ≤ S := by
    dsimp [S]
    nlinarith [Real.rpow_nonneg heps_nonneg (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)),
      Real.rpow_nonneg hdelta_nonneg (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)),
      Real.rpow_nonneg hgamma_nonneg (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)),
      Real.rpow_nonneg hzeta_nonneg (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))]
  have hmdq_le : ((params.m * params.d : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) ≤
      ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * R := by
    calc
      ((params.m * params.d : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)
        = (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * ratio := by
            simp [ratio, Nat.cast_mul, div_eq_mul_inv, mul_comm, mul_left_comm]
      _ ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * R := by
            exact mul_le_mul_of_nonneg_left hratio_le_R (by positivity)
      _ ≤ ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * R := by
            have hm_le : (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ≤ ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
              nlinarith [hk2_ge_one, show 0 ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) by positivity]
            exact mul_le_mul_of_nonneg_right hm_le hR_nonneg
  have hone_div_le_ratio : 1 / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) ≤ ratio := by
    dsimp [ratio]
    exact div_le_div_of_nonneg_right hd_ge_one hq_pos.le
  have hdnoteq_le : ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) ≤
      ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * R := by
    calc
      ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)
        = ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (1 / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) := by ring
      _ ≤ ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * R := by
            exact mul_le_mul_of_nonneg_left (le_trans hone_div_le_ratio hratio_le_R)
              (by positivity)
      _ ≤ ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * R := by
            have hk2_le : ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) ≤
                ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
              nlinarith [hm_ge_one, show 0 ≤ ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) by positivity]
            exact mul_le_mul_of_nonneg_right hk2_le hR_nonneg
  have hsmall : ((params.m * params.d : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) +
        ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) ≤
      2 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * S := by
    have hsum : ((params.m * params.d : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) +
          ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) ≤
        2 * (((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * R) := by
      nlinarith [hmdq_le, hdnoteq_le]
    have hRS : 2 * (((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * R) ≤
        2 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * S := by
      have hfactor_nonneg : 0 ≤ 2 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
        positivity
      calc
        2 * (((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * R)
          = (2 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error)) * R := by ring
        _ ≤ (2 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error)) * S := by
              exact mul_le_mul_of_nonneg_left hR_le_S hfactor_nonneg
        _ = 2 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * S := by ring
    exact le_trans hsum hRS
  dsimp only [_root_.LIDT.MIPStarRE.LDT.Pasting.hBConsistencyError, _root_.LIDT.MIPStarRE.LDT.Pasting.overAllOutcomesError]
  linarith [hsmall]
