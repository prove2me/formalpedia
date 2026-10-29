-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_endpoint_comm_error_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:24:55.139103+00:00
-- url     : https://prove2.me/submissions/d5c41940-8a9e-4354-a171-7dfcf35ccc4c

-- Generated proof for MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_endpoint_comm_error_le.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_PrefixMoved
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_ldSandwichLineOnePoint_endpoint_sqrt_bound

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
# Section 12 pasting: line one-point transport — outcome lemmas

Internal helper module; part of the file-split for `#1127`.

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























-- This arithmetic absorption proof expands several nested error estimates from the paper.

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (eps delta gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error) {j k : ℕ}
    (hj_pos : 1 ≤ j) (hjk : j ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1) :
    zeta + Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * min eps 1 + 4 * min delta 1) +
        2 * Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta j) ≤
      _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointError params eps delta gamma zeta k := by
  have hm_ge_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hk_ge_j : (j : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) := by exact_mod_cast hjk
  have hratio_nonneg : 0 ≤ ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    positivity
  let E : _root_.LIDT.MIPStarRE.LDT.Error := Real.rpow eps (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))
  let D : _root_.LIDT.MIPStarRE.LDT.Error := Real.rpow delta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))
  let Γ : _root_.LIDT.MIPStarRE.LDT.Error := Real.rpow gamma (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))
  let Z : _root_.LIDT.MIPStarRE.LDT.Error := Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))
  let R : _root_.LIDT.MIPStarRE.LDT.Error := Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))
  let S : _root_.LIDT.MIPStarRE.LDT.Error := E + D + Γ + Z + R
  let T : _root_.LIDT.MIPStarRE.LDT.Error := Γ + Z + R
  have hE_nonneg : 0 ≤ E := by dsimp [E]; exact Real.rpow_nonneg heps_nonneg _
  have hD_nonneg : 0 ≤ D := by dsimp [D]; exact Real.rpow_nonneg hdelta_nonneg _
  have hΓ_nonneg : 0 ≤ Γ := by dsimp [Γ]; exact Real.rpow_nonneg hgamma_nonneg _
  have hZ_nonneg : 0 ≤ Z := by dsimp [Z]; exact Real.rpow_nonneg hzeta_nonneg _
  have hR_nonneg : 0 ≤ R := by dsimp [R]; exact Real.rpow_nonneg hratio_nonneg _
  have hzeta_le_Z : zeta ≤ Z := by
    dsimp [Z]
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta_le
        (by norm_num : 0 ≤ (1 / (32 : Error)))
        (by norm_num : (1 / (32 : Error)) ≤ (1 : Error)))
  have hzeta_bound : zeta ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Z := by
    calc
      zeta ≤ Z := hzeta_le_Z
      _ = 1 * Z := by ring
      _ ≤ ((k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error)) * Z := by
            have hkm_ge_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
              have hk_ge_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) := by
                calc
                  (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (j : _root_.LIDT.MIPStarRE.LDT.Error) := by exact_mod_cast hj_pos
                  _ ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) := hk_ge_j
              calc
                (1 : _root_.LIDT.MIPStarRE.LDT.Error) = 1 * 1 := by ring
                _ ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
                  exact mul_le_mul hk_ge_one hm_ge_one (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_right hkm_ge_one hZ_nonneg
      _ = (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Z := by ring
  have hsqrt_endpoint :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_endpoint_sqrt_bound params eps delta k
      (by
        calc
          1 ≤ j := hj_pos
          _ ≤ k := hjk)
      heps_nonneg hdelta_nonneg
  have hsqrt_bound :
      Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * min eps 1 + 4 * min delta 1) ≤
        3 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * (E + D)) := by
    calc
      Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * min eps 1 + 4 * min delta 1)
          ≤ 3 * (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * (E + D) := by
            simpa [E, D, mul_assoc] using hsqrt_endpoint
      _ = 3 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * (E + D)) := by ring
  let sixteenthSum : _root_.LIDT.MIPStarRE.LDT.Error :=
    Real.rpow gamma (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) +
      Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) +
      Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error))
  let thirtysecondSum : _root_.LIDT.MIPStarRE.LDT.Error := T
  have hgamma32_sq :
      Γ ^ (2 : ℕ) = Real.rpow gamma (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    dsimp [Γ]
    calc
      (Real.rpow gamma (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ)
          = (Real.rpow gamma (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : _root_.LIDT.MIPStarRE.LDT.Error) := by norm_num
      _ = Real.rpow gamma ((1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) * (2 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            symm
            exact Real.rpow_mul hgamma_nonneg _ _
      _ = Real.rpow gamma (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by norm_num
  have hzeta32_sq :
      Z ^ (2 : ℕ) = Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    dsimp [Z]
    calc
      (Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ)
          = (Real.rpow zeta (1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : _root_.LIDT.MIPStarRE.LDT.Error) := by norm_num
      _ = Real.rpow zeta ((1 / (32 : _root_.LIDT.MIPStarRE.LDT.Error)) * (2 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            symm
            exact Real.rpow_mul hzeta_nonneg _ _
      _ = Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by norm_num
  have hratio32_sq :
      R ^ (2 : ℕ) =
        Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    dsimp [R]
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
    have hsq : Γ ^ (2 : ℕ) + Z ^ (2 : ℕ) + R ^ (2 : ℕ) ≤ (Γ + Z + R) ^ (2 : ℕ) := by
      nlinarith [hΓ_nonneg, hZ_nonneg, hR_nonneg]
    rw [hgamma32_sq, hzeta32_sq, hratio32_sq] at hsq
    simpa [sixteenthSum, thirtysecondSum, T] using hsq
  have hsixteenth_nonneg : 0 ≤ sixteenthSum := by
    dsimp [sixteenthSum]
    positivity
  have hcomm_sqrt :
      Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta j) ≤
        21 * (j : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * T := by
    have hright_nonneg : 0 ≤ 21 * (j : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * T := by
      positivity
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · exact hright_nonneg
    · have hm_sq_ge : (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ) := by
        nlinarith [hm_ge_one]
      calc
        _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta j
            = 426 * ((j : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * sixteenthSum := by
              simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError, sixteenthSum]
        _ ≤ 441 * ((j : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * sixteenthSum := by
              have hcoef :
                  426 * ((j : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ≤
                    441 * ((j : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
                have hbase : (426 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 441 := by norm_num
                have htail_nonneg : 0 ≤ ((j : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
                  positivity
                simpa [mul_assoc] using mul_le_mul_of_nonneg_right hbase htail_nonneg
              exact mul_le_mul_of_nonneg_right hcoef hsixteenth_nonneg
        _ ≤ 441 * ((j : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) *
              (thirtysecondSum ^ (2 : ℕ)) := by
              have hcoef_nonneg : 0 ≤ 441 * ((j : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
                positivity
              exact mul_le_mul_of_nonneg_left hsixteenth_le_thirtysecond_sq hcoef_nonneg
        _ ≤ 441 * ((j : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) *
              (thirtysecondSum ^ (2 : ℕ)) := by
              gcongr
        _ = (21 * (j : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * T) ^ (2 : ℕ) := by
              simp [thirtysecondSum]
              ring
  have hcomm_bound :
      2 * Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta j) ≤
        42 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * T) := by
    have hjT_to_kT : (j : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * T ≤
        (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * T := by
      have hmT_nonneg : 0 ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * T := by positivity
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hk_ge_j hmT_nonneg
    calc
      2 * Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta j)
          ≤ 2 * (21 * (j : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * T) := by
            exact mul_le_mul_of_nonneg_left hcomm_sqrt (by norm_num)
      _ = 42 * ((j : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * T) := by ring
      _ ≤ 42 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * T) := by
            exact mul_le_mul_of_nonneg_left hjT_to_kT (by norm_num)
  have hcomponent :
      (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Z +
          3 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * (E + D)) +
          42 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * T) ≤
        43 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * S) := by
    have hleft_nonneg : 0 ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by positivity
    dsimp [S, T]
    nlinarith [hleft_nonneg, hE_nonneg, hD_nonneg, hΓ_nonneg, hZ_nonneg, hR_nonneg]
  calc
    zeta + Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * min eps 1 + 4 * min delta 1) +
        2 * Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta j)
        ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Z +
            3 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * (E + D)) +
            42 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * T) := by
          nlinarith [hzeta_bound, hsqrt_bound, hcomm_bound]
    _ ≤ 43 * ((k : _root_.LIDT.MIPStarRE.LDT.Error) * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * S) := hcomponent
    _ = _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointError params eps delta gamma zeta k := by
          simp [_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointError, S, E, D, Γ, Z, R]
          ring
