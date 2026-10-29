-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.commutingWithGComplete_ofComMainAndSelfConsistency
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:47:16.390859+00:00
-- url     : https://prove2.me/submissions/c2dc99fd-548a-4b54-ac88-8c6b0ea89fa1

-- Generated proof for MIPStarRE.LDT.Pasting.commutingWithGComplete_ofComMainAndSelfConsistency.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_commutativitySwitcheroo_ofCompleteSelfConsistency
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_completePartAggregateCommutation_as_total
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_completePartProjFamily_selfConsistency_generic
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_firstSwitcherooError_le_commutingWithGCompleteError
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_firstSwitcherooError_le_eighth_stage
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_pointWithCompletePart_as_switcheroo_input
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_sddOpRel_swap_questions
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_qSDDOp_symm

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

/- Source helpers from MIPStarRE/LDT/Pasting/CommutingWithG/Complete.lean. -/
/-!
# Section 12 pasting: commuting-with-G complete part

Complete-part commuting-with-`G` bounds.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The paper's scalar inequality
`12·√ζ + 4·√θ₁ ≤ ν₂`, where `θ₁ = θ(ζ, ζ, comMainError)` is the first
switcheroo error. The proof uses `firstSwitcherooError_le_eighth_stage` to bound
`θ₁` by `36m · eighthSum`, then a sqrt/rpow chain to land on
`ν₂ = commutingWithGCompleteError`. -/
private lemma secondSwitcherooError_le_commutingWithGCompleteError
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q) :
    commutativitySwitcherooError zeta zeta
      (commutativitySwitcherooError zeta zeta
        (Commutativity.comMainError params gamma zeta))
      ≤ commutingWithGCompleteError params gamma zeta := by
  have hm_nonneg : 0 ≤ (params.m : Error) := by positivity
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hq_pos : (0 : Error) < params.q := by
    exact_mod_cast params.hq
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hratio_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 := by
    exact (div_le_one hq_pos).2 (by simpa using hd_le_q)
  let eighthSum : Error :=
    Real.rpow gamma (1 / (8 : Error)) +
      Real.rpow zeta (1 / (8 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error))
  let sixteenthSum : Error :=
    Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
  have hsixteenth_nonneg : 0 ≤ sixteenthSum := by
    dsimp [sixteenthSum]
    positivity
  have hsqrt_m_le : Real.sqrt (params.m : Error) ≤ (params.m : Error) := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · exact hm_nonneg
    · nlinarith
  have hgamma_sixteen_sq :
      (Real.rpow gamma (1 / (16 : Error))) ^ (2 : ℕ) =
        Real.rpow gamma (1 / (8 : Error)) := by
    calc
      (Real.rpow gamma (1 / (16 : Error))) ^ (2 : ℕ)
          = (Real.rpow gamma (1 / (16 : Error))) ^ (2 : Error) := by norm_num
      _ = Real.rpow gamma ((1 / (16 : Error)) * (2 : Error)) := by
            symm
            exact Real.rpow_mul hgamma_nonneg _ _
      _ = Real.rpow gamma (1 / (8 : Error)) := by norm_num
  have hzeta_sixteen_sq :
      (Real.rpow zeta (1 / (16 : Error))) ^ (2 : ℕ) =
        Real.rpow zeta (1 / (8 : Error)) := by
    calc
      (Real.rpow zeta (1 / (16 : Error))) ^ (2 : ℕ)
          = (Real.rpow zeta (1 / (16 : Error))) ^ (2 : Error) := by norm_num
      _ = Real.rpow zeta ((1 / (16 : Error)) * (2 : Error)) := by
            symm
            exact Real.rpow_mul hzeta_nonneg _ _
      _ = Real.rpow zeta (1 / (8 : Error)) := by norm_num
  have hratio_sixteen_sq :
      (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))) ^ (2 : ℕ) =
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error)) := by
    calc
      (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))) ^ (2 : ℕ)
          =
            (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))) ^
              (2 : Error) := by norm_num
      _ =
          Real.rpow (((params.d : Error) / (params.q : Error)))
            ((1 / (16 : Error)) * (2 : Error)) := by
              symm
              exact Real.rpow_mul hratio_nonneg _ _
      _ = Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error)) := by
            norm_num
  have heighth_le_sixteenth_sq : eighthSum ≤ sixteenthSum ^ (2 : ℕ) := by
    let a : Error := Real.rpow gamma (1 / (16 : Error))
    let b : Error := Real.rpow zeta (1 / (16 : Error))
    let c : Error := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
    have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
    have hb_nonneg : 0 ≤ b := by dsimp [b]; positivity
    have hc_nonneg : 0 ≤ c := by dsimp [c]; positivity
    have hsq : a ^ (2 : ℕ) + b ^ (2 : ℕ) + c ^ (2 : ℕ) ≤ (a + b + c) ^ (2 : ℕ) := by
      nlinarith [ha_nonneg, hb_nonneg, hc_nonneg]
    rw [hgamma_sixteen_sq, hzeta_sixteen_sq, hratio_sixteen_sq] at hsq
    simpa [a, b, c, eighthSum, sixteenthSum] using hsq
  have hsqrt_eighth : Real.sqrt eighthSum ≤ sixteenthSum := by
    exact (Real.sqrt_le_iff).2 ⟨hsixteenth_nonneg, by simpa using heighth_le_sixteenth_sq⟩
  have hsqrt_theta1 :
      Real.rpow
        (commutativitySwitcherooError zeta zeta
          (Commutativity.comMainError params gamma zeta))
        (1 / (2 : Error)) ≤ 6 * (params.m : Error) * sixteenthSum := by
    have hsqrt36 : Real.sqrt (36 : Error) = 6 := by norm_num
    have hsqrt_theta1' :
        Real.sqrt
          (commutativitySwitcherooError zeta zeta
            (Commutativity.comMainError params gamma zeta))
          ≤ 6 * (params.m : Error) * sixteenthSum := by
      calc
        Real.sqrt
            (commutativitySwitcherooError zeta zeta
              (Commutativity.comMainError params gamma zeta))
          ≤ Real.sqrt (36 * (params.m : Error) * eighthSum) := by
              have htheta1_bound :=
                firstSwitcherooError_le_eighth_stage params gamma zeta
                  hgamma_nonneg hzeta_nonneg hzeta hd_le_q
              exact Real.sqrt_le_sqrt htheta1_bound
        _ = Real.sqrt (36 : Error) * Real.sqrt ((params.m : Error) * eighthSum) := by
              rw [show (36 * (params.m : Error) * eighthSum) =
                (36 : Error) * ((params.m : Error) * eighthSum) by ring]
              rw [Real.sqrt_mul (by positivity)]
        _ = 6 * (Real.sqrt (params.m : Error) * Real.sqrt eighthSum) := by
              rw [hsqrt36, Real.sqrt_mul hm_nonneg]
        _ ≤ 6 * ((params.m : Error) * Real.sqrt eighthSum) := by
              gcongr
        _ ≤ 6 * ((params.m : Error) * sixteenthSum) := by
              gcongr
        _ = 6 * (params.m : Error) * sixteenthSum := by ring
    simpa [Real.sqrt_eq_rpow] using hsqrt_theta1'
  have hhalf_zeta :
      Real.rpow zeta (1 / (2 : Error)) ≤ Real.rpow zeta (1 / (16 : Error)) := by
    have hpow : (1 / (16 : Error)) ≤ (1 / (2 : Error)) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta (by norm_num) hpow
  have hgamma16_nonneg : 0 ≤ Real.rpow gamma (1 / (16 : Error)) := by
    exact Real.rpow_nonneg hgamma_nonneg _
  have hratio16_nonneg :
      0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
    exact Real.rpow_nonneg hratio_nonneg _
  have hzeta_term :
      12 * Real.rpow zeta (1 / (2 : Error)) ≤ 12 * (params.m : Error) * sixteenthSum := by
    have hsum1 :
        Real.rpow zeta (1 / (16 : Error)) ≤
          Real.rpow gamma (1 / (16 : Error)) + Real.rpow zeta (1 / (16 : Error)) := by
      linarith
    have hsum2 :
        Real.rpow gamma (1 / (16 : Error)) + Real.rpow zeta (1 / (16 : Error)) ≤
          sixteenthSum := by
      have hsum2' :
          Real.rpow gamma (1 / (16 : Error)) + Real.rpow zeta (1 / (16 : Error)) ≤
            Real.rpow gamma (1 / (16 : Error)) + Real.rpow zeta (1 / (16 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
        linarith
      simpa [sixteenthSum] using hsum2'
    have hterm : Real.rpow zeta (1 / (2 : Error)) ≤ sixteenthSum := by
      exact le_trans hhalf_zeta (le_trans hsum1 hsum2)
    calc
      12 * Real.rpow zeta (1 / (2 : Error)) ≤ 12 * sixteenthSum := by
        gcongr
      _ ≤ 12 * ((params.m : Error) * sixteenthSum) := by
        nlinarith [hm_ge_one, hsixteenth_nonneg]
      _ = 12 * (params.m : Error) * sixteenthSum := by ring
  have hchi_term :
      4 * Real.rpow
        (commutativitySwitcherooError zeta zeta
          (Commutativity.comMainError params gamma zeta))
        (1 / (2 : Error)) ≤ 24 * (params.m : Error) * sixteenthSum := by
    nlinarith [hsqrt_theta1]
  calc
    commutativitySwitcherooError zeta zeta
      (commutativitySwitcherooError zeta zeta
        (Commutativity.comMainError params gamma zeta))
      = 12 * Real.rpow zeta (1 / (2 : Error)) +
          4 * Real.rpow
            (commutativitySwitcherooError zeta zeta
              (Commutativity.comMainError params gamma zeta))
            (1 / (2 : Error)) := by
              simp [commutativitySwitcherooError]
              ring
    _ ≤ 12 * (params.m : Error) * sixteenthSum +
          24 * (params.m : Error) * sixteenthSum := by
            nlinarith [hzeta_term, hchi_term]
    _ = commutingWithGCompleteError params gamma zeta := by
          simp [commutingWithGCompleteError, sixteenthSum]
          ring





end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/SwitcherooCompletion/Utilities.lean. -/
/-!
# Section 12 pasting: switcheroo completion utilities

Post-theorem convenience lemmas: question-swapping, complete-part
reinterpretations, and self-consistency inheritance.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





/-- The complete-part family inherits self-consistency from the slice family by
pointwise comparison of the `qSDD` defect. -/
lemma completePartProjFamily_selfConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : GCompleteSelfConsistencyStatement params strategy.state family zeta) :
    SDDRel strategy.state
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft params (completePartProjFamily params family))
      (switcherooSelfConsistencyRight params (completePartProjFamily params family))
      zeta := by
  simpa using
    completePartProjFamily_selfConsistency_generic params strategy.state family zeta hself

end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Preliminaries/DistanceBounds.lean. -/
/-!
# Preliminary comparison theorems: distance bounds

Triangle-inequality style bounds for `SDDRel` and `SDDOpRel`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-! ### Infrastructure: triangle inequality for `SDDRel` -/















/-! ### Infrastructure: triangle inequality for `SDDOpRel` -/









/-- Symmetry of the operator-family state-dependent distance relation. -/
lemma sddOpRel_symm
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ : Error) :
    SDDOpRel ψ 𝒟 A B δ → SDDOpRel ψ 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  simpa [sddErrorOp, qSDDOp_symm] using h




end MIPStarRE.LDT.Preliminaries

end

end LIDT

open LIDT
/-!
# Section 12 pasting: commuting-with-G complete part

Complete-part commuting-with-`G` bounds.
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
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q)
    (hcom : _root_.LIDT.MIPStarRE.LDT.Commutativity.ComMainConclusion params strategy family gamma zeta)
    (hself : _root_.LIDT.MIPStarRE.LDT.Pasting.GCompleteSelfConsistencyStatement params strategy.state family zeta) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.CommutingWithGCompleteStatement params strategy.state family gamma zeta := by
  have hswitch₁ :
      _root_.LIDT.MIPStarRE.LDT.Pasting.CommutativitySwitcherooStatement params strategy.state family family.meas
        zeta zeta (_root_.LIDT.MIPStarRE.LDT.Pasting.pairwiseCompletePartCommutationError params gamma zeta) := by
    simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.pairwiseCompletePartCommutationError] using
      _root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcheroo_ofCompleteSelfConsistency params strategy.state strategy.isNormalized
        strategy.densityFixed
        family family.meas zeta zeta
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError params gamma zeta)
        hself hself.completePartSelfConsistency hcom
  have hpoint_raw :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
        (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductLeft params family)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductRight params family)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError zeta zeta
          (_root_.LIDT.MIPStarRE.LDT.Pasting.pairwiseCompletePartCommutationError params gamma zeta)) := by
      have hswap :=
        _root_.LIDT.MIPStarRE.LDT.Pasting.sddOpRel_swap_questions params strategy.state
          (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeft params family family.meas)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateRight params family family.meas)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError zeta zeta
            (_root_.LIDT.MIPStarRE.LDT.Pasting.pairwiseCompletePartCommutationError params gamma zeta))
          hswitch₁.aggregateCommutation
      have hsymm :=
        _root_.LIDT.MIPStarRE.LDT.Preliminaries.sddOpRel_symm strategy.state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
          (fun q => (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeft params family family.meas) (q.2, q.1))
          (fun q => (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateRight params family family.meas) (q.2, q.1))
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError zeta zeta
            (_root_.LIDT.MIPStarRE.LDT.Pasting.pairwiseCompletePartCommutationError params gamma zeta))
          hswap
      refine ⟨?_⟩
      simpa [_root_.LIDT.MIPStarRE.LDT.sddErrorOp, _root_.LIDT.MIPStarRE.LDT.qSDDOp, _root_.LIDT.MIPStarRE.LDT.qSDDCore,
        _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeft, _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateRight,
        _root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductLeft, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductRight,
        _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas_total, _root_.LIDT.MIPStarRE.LDT.Pasting.multiplyByTotalOnRight,
        _root_.LIDT.MIPStarRE.LDT.Pasting.multiplyByTotalOnLeft, _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily]
        using hsymm.squaredDistanceBound
  have hpoint :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
        (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductLeft params family)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductRight params family)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGCompleteError params gamma zeta) :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.sddOpRel_mono strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductLeft params family)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartPointProductRight params family)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError zeta zeta
        (_root_.LIDT.MIPStarRE.LDT.Pasting.pairwiseCompletePartCommutationError params gamma zeta))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGCompleteError params gamma zeta)
      hpoint_raw
      (_root_.LIDT.MIPStarRE.LDT.Pasting.firstSwitcherooError_le_commutingWithGCompleteError params gamma zeta
        hgamma_nonneg hgamma hzeta_nonneg hzeta hd_le_q)
  have hswitch₂ :
      _root_.LIDT.MIPStarRE.LDT.Pasting.CommutativitySwitcherooStatement params strategy.state family
        (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily params family)
        zeta zeta
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError zeta zeta
          (_root_.LIDT.MIPStarRE.LDT.Pasting.pairwiseCompletePartCommutationError params gamma zeta)) := by
    apply _root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcheroo_ofCompleteSelfConsistency params strategy.state
      strategy.isNormalized strategy.densityFixed family
      (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily params family) zeta zeta
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError zeta zeta
        (_root_.LIDT.MIPStarRE.LDT.Pasting.pairwiseCompletePartCommutationError params gamma zeta))
    · exact hself
    · exact _root_.LIDT.MIPStarRE.LDT.Pasting.completePartProjFamily_selfConsistency params strategy family zeta hself
    · exact _root_.LIDT.MIPStarRE.LDT.Pasting.pointWithCompletePart_as_switcheroo_input params strategy.state family
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError zeta zeta
          (_root_.LIDT.MIPStarRE.LDT.Pasting.pairwiseCompletePartCommutationError params gamma zeta)) hpoint_raw
  have htotal_raw :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
        (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartTotalProductLeft params family)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartTotalProductRight params family)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError zeta zeta
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError zeta zeta
            (_root_.LIDT.MIPStarRE.LDT.Pasting.pairwiseCompletePartCommutationError params gamma zeta))) := by
    exact _root_.LIDT.MIPStarRE.LDT.Pasting.completePartAggregateCommutation_as_total params strategy.state family
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError zeta zeta
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError zeta zeta
          (_root_.LIDT.MIPStarRE.LDT.Pasting.pairwiseCompletePartCommutationError params gamma zeta)))
      hswitch₂.aggregateCommutation
  refine ⟨?_, hpoint, ?_⟩
  · refine ⟨?_⟩
    simpa [_root_.LIDT.MIPStarRE.LDT.sddErrorOp, _root_.LIDT.MIPStarRE.LDT.qSDDOp, _root_.LIDT.MIPStarRE.LDT.qSDDCore, _root_.LIDT.MIPStarRE.LDT.Pasting.pairwiseCompletePartCommutationError,
      _root_.LIDT.MIPStarRE.LDT.Commutativity.ComMainConclusion, _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion, _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion,
      _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceOutcome, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductLeft,
      _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductRight, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceFirstFactor,
      _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceSecondFactor, _root_.LIDT.MIPStarRE.LDT.Commutativity.leftOrderedProductOpFamily,
      _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.orderedProductOpFamily, _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.reversedProductOpFamily, _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily]
      using hcom.squaredDistanceBound
  · exact
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.sddOpRel_mono strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
        (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartTotalProductLeft params family)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartTotalProductRight params family)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError zeta zeta
          (_root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError zeta zeta
            (_root_.LIDT.MIPStarRE.LDT.Pasting.pairwiseCompletePartCommutationError params gamma zeta)))
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGCompleteError params gamma zeta)
        htotal_raw
        (secondSwitcherooError_le_commutingWithGCompleteError params gamma zeta
          hgamma_nonneg hzeta_nonneg hzeta hd_le_q)
