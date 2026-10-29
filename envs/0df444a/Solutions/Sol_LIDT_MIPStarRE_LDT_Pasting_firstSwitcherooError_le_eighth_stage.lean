-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.firstSwitcherooError_le_eighth_stage
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:44:31.681728+00:00
-- url     : https://prove2.me/submissions/5e6be99b-e019-4ef7-9f16-51202e12d41b

-- Generated proof for MIPStarRE.LDT.Pasting.firstSwitcherooError_le_eighth_stage.
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
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError zeta zeta
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError params gamma zeta)
      ≤ 36 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) *
        (Real.rpow gamma (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) +
          Real.rpow zeta (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) +
          Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error))) := by
  have hm_nonneg : 0 ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by positivity
  have hm_ge_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
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
  have heighth_nonneg : 0 ≤ eighthSum := by
    dsimp [eighthSum]
    positivity
  have hhalf_zeta :
      Real.rpow zeta (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ Real.rpow zeta (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    have hpow : (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta (by norm_num) hpow
  have hgamma_eight_sq :
      (Real.rpow gamma (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ) =
        Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    calc
      (Real.rpow gamma (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ)
          = (Real.rpow gamma (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : _root_.LIDT.MIPStarRE.LDT.Error) := by norm_num
      _ = Real.rpow gamma ((1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) * (2 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            symm
            exact Real.rpow_mul hgamma_nonneg _ _
      _ = Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := by norm_num
  have hzeta_eight_sq :
      (Real.rpow zeta (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ) =
        Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    calc
      (Real.rpow zeta (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ)
          = (Real.rpow zeta (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : _root_.LIDT.MIPStarRE.LDT.Error) := by norm_num
      _ = Real.rpow zeta ((1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) * (2 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            symm
            exact Real.rpow_mul hzeta_nonneg _ _
      _ = Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := by norm_num
  have hratio_eight_sq :
      (Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ) =
        Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    calc
      (Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ)
          =
            (Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error))) ^
              (2 : _root_.LIDT.MIPStarRE.LDT.Error) := by norm_num
      _ =
          Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)))
            ((1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) * (2 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
              symm
              exact Real.rpow_mul hratio_nonneg _ _
      _ = Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            norm_num
  have hquarter_le_eighth_sq : quarterSum ≤ eighthSum ^ (2 : ℕ) := by
    let a : _root_.LIDT.MIPStarRE.LDT.Error := Real.rpow gamma (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error))
    let b : _root_.LIDT.MIPStarRE.LDT.Error := Real.rpow zeta (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error))
    let c : _root_.LIDT.MIPStarRE.LDT.Error := Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error))
    have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
    have hb_nonneg : 0 ≤ b := by dsimp [b]; positivity
    have hc_nonneg : 0 ≤ c := by dsimp [c]; positivity
    have hsq : a ^ (2 : ℕ) + b ^ (2 : ℕ) + c ^ (2 : ℕ) ≤ (a + b + c) ^ (2 : ℕ) := by
      nlinarith [ha_nonneg, hb_nonneg, hc_nonneg]
    rw [hgamma_eight_sq, hzeta_eight_sq, hratio_eight_sq] at hsq
    simpa [a, b, c, quarterSum, eighthSum] using hsq
  have hsqrt_quarter : Real.sqrt quarterSum ≤ eighthSum := by
    have heighth_nonneg : 0 ≤ eighthSum := by
      dsimp [eighthSum]
      positivity
    exact (Real.sqrt_le_iff).2 ⟨heighth_nonneg, by simpa using hquarter_le_eighth_sq⟩
  have hsqrt30_le_six : Real.sqrt (30 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 6 := by
    have hsq : (Real.sqrt (30 : _root_.LIDT.MIPStarRE.LDT.Error)) ^ (2 : ℕ) ≤ (6 : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ) := by norm_num
    nlinarith [Real.sq_sqrt (show 0 ≤ (30 : _root_.LIDT.MIPStarRE.LDT.Error) by positivity), hsq]
  have hsqrt_m_le : Real.sqrt (params.m : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · exact hm_nonneg
    · nlinarith
  have hsqrt_com :
      Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError params gamma zeta) ≤
        6 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eighthSum := by
    have hquarter_nonneg : 0 ≤ quarterSum := by
      dsimp [quarterSum]
      positivity
    have hsplit_m_quarter :
        Real.sqrt ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) * quarterSum) =
          Real.sqrt (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Real.sqrt quarterSum := by
      rw [Real.sqrt_mul hm_nonneg]
    calc
      Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError params gamma zeta)
          = Real.sqrt (30 : _root_.LIDT.MIPStarRE.LDT.Error) *
              Real.sqrt ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) * quarterSum) := by
              simp [_root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError, quarterSum]
              ring
      _ = Real.sqrt (30 : _root_.LIDT.MIPStarRE.LDT.Error) * (Real.sqrt (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Real.sqrt quarterSum) := by
            rw [hsplit_m_quarter]
      _ = Real.sqrt (30 : _root_.LIDT.MIPStarRE.LDT.Error) * Real.sqrt (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * Real.sqrt quarterSum := by
            ring
      _ ≤ 6 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eighthSum := by
            gcongr
  have hzeta_term :
      12 * Real.rpow zeta (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ 12 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eighthSum := by
    have hgamma8_nonneg : 0 ≤ Real.rpow gamma (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
      exact Real.rpow_nonneg hgamma_nonneg _
    have hratio8_nonneg :
        0 ≤ Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
      exact Real.rpow_nonneg hratio_nonneg _
    have hsum1 :
        Real.rpow zeta (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
          Real.rpow gamma (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) + Real.rpow zeta (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
      linarith
    have hsum2 :
        Real.rpow gamma (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) + Real.rpow zeta (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ eighthSum := by
      have hsum2' :
          Real.rpow gamma (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) + Real.rpow zeta (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
            Real.rpow gamma (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) + Real.rpow zeta (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
        linarith
      simpa [eighthSum] using hsum2'
    have hterm : Real.rpow zeta (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ eighthSum := by
      exact le_trans hhalf_zeta (le_trans hsum1 hsum2)
    calc
      12 * Real.rpow zeta (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ 12 * eighthSum := by
        gcongr
      _ ≤ 12 * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eighthSum) := by
        nlinarith [hm_ge_one, heighth_nonneg]
      _ = 12 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eighthSum := by ring
  have hchi_term :
      4 * Real.rpow (_root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError params gamma zeta) (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
        24 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eighthSum := by
    have hsqrt_com' :
        Real.rpow (_root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError params gamma zeta) (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)) ≤
          6 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eighthSum := by
      simpa [Real.sqrt_eq_rpow] using hsqrt_com
    nlinarith [hsqrt_com']
  calc
    _root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError zeta zeta (_root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError params gamma zeta)
      = 12 * Real.rpow zeta (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)) +
          4 * Real.rpow (_root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError params gamma zeta) (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commutativitySwitcherooError]
            ring
    _ ≤ 12 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eighthSum +
          24 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eighthSum := by
            nlinarith [hzeta_term, hchi_term]
    _ = 36 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eighthSum := by ring
    _ = 36 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) *
          (Real.rpow gamma (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) +
            Real.rpow zeta (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) +
            Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error))) := by
            simp [eighthSum]
