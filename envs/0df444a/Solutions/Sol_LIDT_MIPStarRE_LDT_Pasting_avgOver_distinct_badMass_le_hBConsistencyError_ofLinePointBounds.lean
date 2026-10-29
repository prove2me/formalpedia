-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.avgOver_distinct_badMass_le_hBConsistencyError_ofLinePointBounds
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:51:31.883007+00:00
-- url     : https://prove2.me/submissions/1bcd18bb-5a78-4317-a8fe-64140a6e3857

-- Generated proof for MIPStarRE.LDT.Pasting.avgOver_distinct_badMass_le_hBConsistencyError_ofLinePointBounds.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_avgOver_uniform_badMass_le_k_mul_ldSandwichLineOnePointError_ofLinePointBounds
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_hBConsistencyBadMass_le_one
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_hBConsistencyBadMass_nonneg
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_ldDnoteq

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

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/LineInterpolation/HBError.lean. -/
/-!
# Line interpolation: H-B consistency error aggregation

Fixed-`u` defect, `hBConsistencyError`, degree-ratio error bounds,
and the final bad-mass aggregation lemma that drives `lem:h-b-consistency`.

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



lemma hBConsistencyError_eq_k_mul_ldSandwichLineOnePointError_add
    (params : Parameters)
    (eps delta gamma zeta : Error) (k : ℕ) :
    hBConsistencyError params eps delta gamma zeta k =
      (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k +
        ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow gamma (1 / (32 : Error)) +
            Real.rpow zeta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
  simp [hBConsistencyError, ldSandwichLineOnePointError]
  ring



lemma one_div_q_le_rpow_degreeRatio
    (params : Parameters) [FieldModel params.q]
    (hd : 0 < params.d) :
    1 / (params.q : Error)
      ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
  let x : Error := ((params.d : Error) / (params.q : Error))
  have hq_pos : 0 < (params.q : Error) := by exact_mod_cast params.hq
  have hx_nonneg : 0 ≤ x := by positivity
  have hqx : 1 / (params.q : Error) ≤ x := by
    have hd_ge_one : (1 : Error) ≤ (params.d : Error) := by exact_mod_cast hd
    simpa [x] using div_le_div_of_nonneg_right hd_ge_one hq_pos.le
  by_cases hx_le_one : x ≤ 1
  · have hx_le_rpow : x ≤ Real.rpow x (1 / (32 : Error)) := by
      simpa [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge' hx_nonneg hx_le_one (by norm_num : 0
            ≤ (1 / (32 : Error)))
          (by norm_num : (1 / (32 : Error)) ≤ (1 : Error)))
    exact le_trans hqx hx_le_rpow
  · have h1_le_x : (1 : Error) ≤ x := le_of_not_ge hx_le_one
    have hq_le_one : 1 / (params.q : Error) ≤ 1 := by
      have hq_ge_one : (1 : Error) ≤ (params.q : Error) := by exact_mod_cast params.hq
      have hq_ne : (params.q : Error) ≠ 0 := by positivity
      field_simp [hq_ne]
      nlinarith
    have h1_le_rpow : (1 : Error) ≤ Real.rpow x (1 / (32 : Error)) := by
      simpa [Real.rpow_one] using
        (Real.rpow_le_rpow (show 0 ≤ (1 : Error) by positivity) h1_le_x (show 0
            ≤ (1 / (32 : Error)) by positivity))
    exact le_trans hq_le_one h1_le_rpow

lemma dnoteq_term_le_hBConsistency_extra
    (params : Parameters) [FieldModel params.q]
    (eps delta gamma zeta : Error)
    (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    ((k : Error) ^ (2 : ℕ)) / (params.q : Error)
      ≤ ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow gamma (1 / (32 : Error)) +
            Real.rpow zeta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
  let S : Error :=
    Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
  have hqterm : 1 / (params.q : Error) ≤ S := by
    have hlast := one_div_q_le_rpow_degreeRatio params hd
    have htail_nonneg :
        0 ≤ Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow gamma (1 / (32 : Error)) +
            Real.rpow zeta (1 / (32 : Error)) :=
      add_nonneg
        (add_nonneg
          (add_nonneg
            (Real.rpow_nonneg heps_nonneg _)
            (Real.rpow_nonneg hdelta_nonneg _))
          (Real.rpow_nonneg hgamma_nonneg _))
        (Real.rpow_nonneg hzeta_nonneg _)
    dsimp [S] at *
    nlinarith
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast (Nat.succ_le_of_lt params.hm)
  have hS_le_mS : S ≤ (params.m : Error) * S := by
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      positivity [heps_nonneg, hdelta_nonneg, hgamma_nonneg, hzeta_nonneg]
    nlinarith
  have hqterm' : 1 / (params.q : Error) ≤ (params.m : Error) * S :=
    le_trans hqterm hS_le_mS
  have hk_nonneg : 0 ≤ ((k : Error) ^ (2 : ℕ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hqterm' hk_nonneg
  simpa [S, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

lemma hBConsistency_error_bound
    (params : Parameters) [FieldModel params.q]
    (eps delta gamma zeta : Error)
    (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k +
        ((k : Error) ^ (2 : ℕ)) / (params.q : Error)
      ≤ hBConsistencyError params eps delta gamma zeta k := by
  rw [hBConsistencyError_eq_k_mul_ldSandwichLineOnePointError_add]
  have hextra := dnoteq_term_le_hBConsistency_extra params eps delta gamma zeta k hd
    heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  linarith



lemma avgOver_distinct_badMass_le_avgOver_uniform_badMass_add_dnoteq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) :
    avgOver (distinctTupleDistribution params k) (fun xs =>
      hBConsistencyBadMass params strategy family u xs)
      ≤ avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs) +
          ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
  calc
    avgOver (distinctTupleDistribution params k) (fun xs =>
        hBConsistencyBadMass params strategy family u xs)
      ≤ avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs) +
          totalVariationDistance
            (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k) := by
            exact avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k params k
              (fun xs => hBConsistencyBadMass params strategy family u xs)
              (fun xs => hBConsistencyBadMass_nonneg params strategy family u xs)
              (fun xs => hBConsistencyBadMass_le_one params strategy family u xs)
    _ ≤ avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs) +
          ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
            gcongr
            exact ldDnoteq params k









end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Line interpolation: H-B consistency error aggregation

Fixed-`u` defect, `hBConsistencyError`, degree-ratio error bounds,
and the final bad-mass aggregation lemma that drives `lem:h-b-consistency`.

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
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (eps delta gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error) (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hline : ∀ i : ℕ, i < k →
      _root_.LIDT.MIPStarRE.LDT.Pasting.LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) (fun xs =>
          _root_.LIDT.MIPStarRE.LDT.Pasting.hBConsistencyBadMass params strategy family u xs)) ≤
      _root_.LIDT.MIPStarRE.LDT.Pasting.hBConsistencyError params eps delta gamma zeta k := by
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k) (fun xs =>
          _root_.LIDT.MIPStarRE.LDT.Pasting.hBConsistencyBadMass params strategy family u xs))
      ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)) (fun xs =>
            _root_.LIDT.MIPStarRE.LDT.Pasting.hBConsistencyBadMass params strategy family u xs) +
          ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error)) := by
          exact _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ (fun u =>
            _root_.LIDT.MIPStarRE.LDT.Pasting.avgOver_distinct_badMass_le_avgOver_uniform_badMass_add_dnoteq
              params strategy family u)
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) (fun u =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k)) (fun xs =>
            _root_.LIDT.MIPStarRE.LDT.Pasting.hBConsistencyBadMass params strategy family u xs)) +
        ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) := by
          rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add]
          simpa using _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const (α := _root_.LIDT.MIPStarRE.LDT.Point params)
            (((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))
    _ ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) * _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointError params eps delta gamma zeta k +
          ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) := by
          gcongr
          exact _root_.LIDT.MIPStarRE.LDT.Pasting.avgOver_uniform_badMass_le_k_mul_ldSandwichLineOnePointError_ofLinePointBounds
            params strategy family eps delta gamma zeta k hline
    _ ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.hBConsistencyError params eps delta gamma zeta k := by
          exact _root_.LIDT.MIPStarRE.LDT.Pasting.hBConsistency_error_bound params eps delta gamma zeta k hd
            heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
