-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_endpoint_ldGbcon_lift_of_axis_self
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:35:13.929245+00:00
-- url     : https://prove2.me/submissions/7201138f-1971-4548-9830-598c0d6bc5b4

-- Generated proof for MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_endpoint_ldGbcon_lift_of_axis_self.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_ldSandwichLineOnePoint_endpoint_ldGbcon_of_axis_self
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_consRel_uniform_equiv
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_consRel_uniform_prod_fst

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

lemma postprocess_postprocess
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (A : SubMeas α ι) (f : α → β) (g : β → γ) :
    postprocess (postprocess A f) g = postprocess A (g ∘ f) := by
  classical
  refine SubMeas.ext ?_ ?_
  · intro c
    simp [postprocess, Function.comp, Finset.sum_filter, Finset.sum_comm, eq_comm]
  · simp [postprocess_total]





















end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/Endpoint.lean. -/
/-!
# Section 12 pasting: line one-point transport — endpoint lemmas

Internal helper module; part of the file-split for `#1127`.

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



lemma ldSandwichLineOnePointRightEndpointMeasurement_toSubMeas
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ux : Point params × Fq params) :
    (ldSandwichLineOnePointRightEndpointMeasurement params strategy ux).toSubMeas =
      postprocess (verticalLineMeasurementFamily params strategy ux.1) (fun f => f ux.2) := by
  simp [ldSandwichLineOnePointRightEndpointMeasurement, verticalLineMeasurementFamily,
    postprocessMeasurement]



-- The proof lifts the endpoint consistency relation through the split
-- sandwiched-line equivalence; the chain of rewriting identities unfolds this
-- equivalence and the endpoint-family definition.



















end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: line one-point transport — endpoint lemmas

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







-- The proof lifts the endpoint consistency relation through the split
-- sandwiched-line equivalence; the chain of rewriting identities unfolds this
-- equivalence and the endpoint-family definition.

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (eps delta zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (k i : ℕ) (hi : i < k) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k))
      (fun q =>
        _root_.LIDT.MIPStarRE.LDT.postprocess
          (_root_.LIDT.MIPStarRE.LDT.evaluateAt params q.1 ((family.meas (q.2 ⟨i, hi⟩)).toSubMeas))
          some)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i)
      (zeta + Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps + 4 * delta)) := by
  let iFin : Fin k := ⟨i, hi⟩
  let Rest := {j : Fin k // j ≠ iFin} → _root_.LIDT.MIPStarRE.LDT.Fq params
  let e := _root_.LIDT.MIPStarRE.LDT.Pasting.sandwichedLineQuestionSplitAtEquiv params iFin
  let endpointLeft : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas (_root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k) (Option (_root_.LIDT.MIPStarRE.LDT.Fq params)) ι :=
    fun q =>
      _root_.LIDT.MIPStarRE.LDT.postprocess
        (_root_.LIDT.MIPStarRE.LDT.evaluateAt params q.1 ((family.meas (q.2 iFin)).toSubMeas))
        some
  let endpointRight : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas (_root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k) (Option (_root_.LIDT.MIPStarRE.LDT.Fq params)) ι :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily params strategy family k i
  have hbase := _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_endpoint_ldGbcon_of_axis_self
    params strategy eps delta zeta haxis hself family hcons
  have hprod :
      _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution ((_root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Fq params) × Rest))
        (fun q =>
          _root_.LIDT.MIPStarRE.LDT.postprocess
            (_root_.LIDT.MIPStarRE.LDT.evaluateAt params q.1.1 ((family.meas q.1.2).toSubMeas))
            some)
        (fun q =>
          _root_.LIDT.MIPStarRE.LDT.postprocess
            (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightEndpointMeasurement params strategy q.1).toSubMeas
            some)
        (zeta + Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps + 4 * delta)) := by
    exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.consRel_uniform_prod_fst strategy.state
      (fun ux : _root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Fq params =>
        _root_.LIDT.MIPStarRE.LDT.postprocess (_root_.LIDT.MIPStarRE.LDT.evaluateAt params ux.1 ((family.meas ux.2).toSubMeas)) some)
      (fun ux : _root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Fq params =>
        _root_.LIDT.MIPStarRE.LDT.postprocess
          (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightEndpointMeasurement params strategy ux).toSubMeas
          some)
      (zeta + Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps + 4 * delta)) hbase
  have hlift :=
    (_root_.LIDT.MIPStarRE.LDT.Preliminaries.consRel_uniform_equiv e strategy.state endpointLeft endpointRight
      (zeta + Real.sqrt (8 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) * eps + 4 * delta))).2
      (by
        convert hprod using 2
        · simp [e, endpointLeft, iFin,
            _root_.LIDT.MIPStarRE.LDT.Pasting.sandwichedLineQuestionSplitAtEquiv]
        · simp only [ne_eq, _root_.LIDT.MIPStarRE.LDT.Pasting.sandwichedLineQuestionSplitAtEquiv, Equiv.coe_fn_symm_mk,
            _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightFamily, hi, ↓reduceDIte, Equiv.funSplitAt_symm_apply,
            _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointRightEndpointMeasurement_toSubMeas, endpointRight, iFin, e]
          exact (_root_.LIDT.MIPStarRE.LDT.Pasting.postprocess_postprocess _ _ _).symm)
  simpa [endpointLeft, endpointRight, iFin] using hlift
