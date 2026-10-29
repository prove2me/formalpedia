-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:17:05.54499+00:00
-- url     : https://prove2.me/submissions/cdf8ee6c-2c38-49b1-9577-93b852579252

-- Generated proof for MIPStarRE.LDT.Pasting.commuteGHalfSandwich_error_bound.
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
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_rpow_oneSixteenth_nonneg

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
# Section 12 pasting: commute G half-sandwich setup — sum bounds

Sum-of-adjoint-products `≤ 1` bounds for the half-product, reverse-half-product,
pair-prefix, and bipartite tensor families. Also contains the error-envelope bound
`commuteGHalfSandwich_error_bound` and its helper `rpow_oneSixteenth_nonneg`.

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

/-! ### Half-product sum bounds -/





/-! ### Error-envelope bound -/

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error) (k : ℕ)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1) :
    3 * (k : _root_.LIDT.MIPStarRE.LDT.Error) *
      (4 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * zeta + (k : _root_.LIDT.MIPStarRE.LDT.Error) * _root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta)
      ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k := by
  let S : _root_.LIDT.MIPStarRE.LDT.Error :=
    Real.rpow gamma (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) +
      Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) +
      Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error))
  have hγterm_nonneg : 0 ≤ Real.rpow gamma (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.rpow_oneSixteenth_nonneg gamma
  have hS_nonneg : 0 ≤ S := by
    have hratio_nonneg : 0 ≤ ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) := by positivity
    dsimp [S]
    exact add_nonneg
      (add_nonneg
        hγterm_nonneg
        (Real.rpow_nonneg hzeta_nonneg (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error))))
      (Real.rpow_nonneg hratio_nonneg (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)))
  have hm_ge_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
    exact_mod_cast (Nat.succ_le_of_lt params.hm)
  have hzeta_to_rpow : zeta ≤ Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    have hpow : (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ (1 : _root_.LIDT.MIPStarRE.LDT.Error) := by norm_num
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta_le (by norm_num) hpow)
  have hzeta_term : zeta ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * S := by
    have hroot_le : Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ S := by
      have hratio_nonneg : 0 ≤ ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) := by positivity
      have hratio_rpow_nonneg :
          0 ≤ Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
        exact Real.rpow_nonneg hratio_nonneg (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error))
      calc
        Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error))
          ≤ Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) + Real.rpow gamma (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
              nlinarith
        _ ≤ Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) + Real.rpow gamma (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
              nlinarith
        _ = S := by
              simp [S, add_assoc, add_comm]
    have hm_mul : Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * S := by
      have : S ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * S := by
        nlinarith
      exact le_trans hroot_le this
    exact le_trans hzeta_to_rpow hm_mul
  calc
    3 * (k : _root_.LIDT.MIPStarRE.LDT.Error) *
      (4 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * zeta + (k : _root_.LIDT.MIPStarRE.LDT.Error) * _root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta)
      = 12 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * zeta +
          3 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * _root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta := by ring
    _ ≤ 12 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) * S) +
          3 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * _root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError params gamma zeta := by
            gcongr
    _ = 12 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) * S) +
          3 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (138 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * S) := by
            simp [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatCommutationError, S]
    _ = 426 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * S := by ring
    _ = _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta k := by
          simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError, S]
