-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.firstSwitcherooError_le_commutingWithGCompleteError
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:48:09.400189+00:00
-- url     : https://prove2.me/submissions/57decbb6-1064-47f0-a736-01b2166f99f9

-- Generated proof for MIPStarRE.LDT.Pasting.firstSwitcherooError_le_commutingWithGCompleteError.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
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
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_firstSwitcherooError_le_eighth_stage

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
# Section 12 pasting: complete-part reductions

Complete-part aggregate commutation and scalar error bounds.
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
    (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError zeta zeta
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError params gamma zeta)
      ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGCompleteError params gamma zeta := by
  have hq_pos : (0 : _root_.LIDT.MIPStarRE.LDT.Error) < params.q := by
    exact_mod_cast params.hq
  have hratio_nonneg : 0 ≤ ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    positivity
  have hratio_le_one : ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ 1 := by
    exact (div_le_one hq_pos).2 (by simpa using hd_le_q)
  let quarterSum : _root_.LIDT.MIPStarRE.LDT.Error :=
    Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) +
      Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) +
      Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))
  let eighthSum : _root_.LIDT.MIPStarRE.LDT.Error :=
    Real.rpow gamma (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) +
      Real.rpow zeta (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) +
      Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error))
  let sixteenthSum : _root_.LIDT.MIPStarRE.LDT.Error :=
    Real.rpow gamma (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) +
      Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) +
      Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error))
  have heighth_gamma :
      Real.rpow gamma (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ Real.rpow gamma (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    have hpow : (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_ge' hgamma_nonneg hgamma (by norm_num) hpow
  have heighth_zeta :
      Real.rpow zeta (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ Real.rpow zeta (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    have hpow : (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta (by norm_num) hpow
  have heighth_ratio :
      Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
        Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    have hpow : (1 / (16 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_ge' hratio_nonneg hratio_le_one (by norm_num) hpow
  have hsixteenth_nonneg : 0 ≤ sixteenthSum := by
    dsimp [sixteenthSum]
    positivity
  have heighth_le_sixteenth : eighthSum ≤ sixteenthSum := by
    dsimp [eighthSum, sixteenthSum]
    exact add_le_add (add_le_add heighth_gamma heighth_zeta) heighth_ratio
  calc
    _root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError zeta zeta (_root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError params gamma zeta)
      ≤ 36 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eighthSum := by
          exact _root_.LIDT.MIPStarRE.LDT.Pasting.firstSwitcherooError_le_eighth_stage params gamma zeta
            hgamma_nonneg hzeta_nonneg hzeta hd_le_q
    _ ≤ 36 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * sixteenthSum := by
          gcongr
    _ = _root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGCompleteError params gamma zeta := by
          simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commutingWithGCompleteError, sixteenthSum]
