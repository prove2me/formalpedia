-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.hAConsistency_submeas
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T18:03:55.826934+00:00
-- url     : https://prove2.me/submissions/da503ba0-1d8f-45f6-9f5e-230a8a1db206

-- Generated proof for MIPStarRE.LDT.Pasting.hAConsistency_submeas.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_avgOver_distinct_badMass_le_hBConsistencyError_ofLinePointBounds
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_avgOver_distinct_pasted_defect_le_badMass
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_commuteGHalfSandwich_core
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_gHatFacts
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_hAConsistency_submeas_from_lineConsistency_of_axis_self
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_hBConsistency_fixed_u_defect_le_avgOver_distinct
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_ldSandwichLineOnePoint_core_of_axis_self

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

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich.lean. -/
/-!
# Section 12 pasting: commute G half-sandwich

Public statement for `lem:commute-g-half-sandwich`.

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

/-- Internal form of `lem:commute-g-half-sandwich` after applying
`cor:G-hat-facts`.

**Source:** The proof in `references/ldt-paper/ld-pasting.tex:871-910` uses
the completed-measurement self-consistency and commutation estimates from
`cor:G-hat-facts`.  The paper-facing theorem `commuteGHalfSandwich` below
derives those estimates from the source hypotheses. -/
lemma commuteGHalfSandwich_ofGHatFacts
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (k : ℕ)
    (hk : 2 ≤ k)
    (hzeta_le : zeta ≤ 1)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta) :
    CommuteGHalfSandwichStatement params ψbi family gamma zeta k := by
  exact ⟨commuteGHalfSandwich_core params ψbi family gamma zeta k hk
    hzeta_le hfacts.completedSelfConsistency hfacts.completedCommutation⟩



end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/HAConsistency.lean. -/
/-!
# Section 12 pasting: H-A consistency

Vertical-line to point-consistency transport and completed-measurement statement for
`cor:h-a-consistency`.

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





/-- Specialization of `hAConsistency_submeas_from_lineConsistency` to the
constructed pasted submeasurement. -/
private lemma hAConsistency_submeas_core_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hHB : HBConsistencyStatement params strategy family
        eps delta gamma zeta k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
        (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
  exact hAConsistency_submeas_from_lineConsistency_of_axis_self params strategy
    (constructedPastedSubMeas params family k) eps delta gamma zeta
    haxis hself_good hgamma_nonneg hzeta_nonneg k hk_pos hHB.lineConsistency













end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Test/StrategyPolynomialFamilies.lean. -/
/-!
# Polynomial-family interfaces for the low individual degree test

Packaged slice-indexed polynomial-family interfaces extracted from
`MIPStarRE.LDT.Test.Strategy`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Polynomial-family interfaces -/



-- NOTE: no global `Inhabited` instance for `IdxPolyFamily`; without an actual
-- slice family, any default would be a degenerate zero-family placeholder.

namespace IdxPolyFamily



































/-- A family point-consistency witness forces the displayed point-consistency
error parameter `ζ` to be nonnegative. -/
theorem zeta_nonneg_of_consistentWithPoints {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {zeta : Error}
    (hcons : family.ConsistentWithPoints strategy zeta) :
    0 ≤ zeta := by
  exact le_trans
    (bipartiteConsError_nonneg strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      family.evaluatedAtNextPoint)
    hcons.pointConsistency.offDiagonalBound





namespace SliceBoundednessInput







end SliceBoundednessInput

end IdxPolyFamily

end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/Core.lean. -/
/-!
# Section 12 pasting: line one-point transport — core theorems

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









/-- Internal form of `lem:ld-sandwich-line-one-point` after applying
`cor:G-hat-facts`.

**Source:** The proof in `references/ldt-paper/ld-pasting.tex:956-1074` uses
the half-sandwich commutation estimates obtained from `cor:G-hat-facts`.  The
	paper-facing theorem `ldSandwichLineOnePoint` below derives those estimates
	from the source hypotheses. -/
lemma ldSandwichLineOnePoint_ofGHatFacts_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_le : zeta ≤ 1)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hfacts : GHatFactsStatement params strategy.state family gamma zeta)
    (k i : ℕ)
    (hi : i < k) :
    LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i := by
  have hcomm :
      ∀ j : ℕ, 2 ≤ j →
        CommuteGHalfSandwichStatement params strategy.state family
          gamma zeta j := by
    intro j hj
    exact commuteGHalfSandwich_ofGHatFacts params strategy.state family gamma zeta
      j hj hzeta_le hfacts
  exact ⟨ldSandwichLineOnePoint_core_of_axis_self params strategy eps delta gamma zeta
    haxis hself_good hgamma_nonneg hzeta_le family hcons hcomm k i hi⟩

/-- Internal form of `lem:ld-sandwich-line-one-point` after applying
`cor:G-hat-facts`.

This source-facing statement retains the usual good-strategy hypothesis. -/
lemma ldSandwichLineOnePoint_ofGHatFacts
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (_hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (_hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (hfacts : GHatFactsStatement params strategy.state family gamma zeta)
    (k i : ℕ)
    (hi : i < k) :
    LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i := by
  have hgamma_nonneg : 0 ≤ gamma :=
    gamma_nonneg_of_isGood params.next strategy hgood
  exact ldSandwichLineOnePoint_ofGHatFacts_of_axis_self params strategy eps delta gamma zeta
    hgood.axisParallelTest hgood.selfConsistencyTest hgamma_nonneg hzeta_le family hcons
    hfacts k i hi

/-- `lem:ld-sandwich-line-one-point`, source-facing form. -/
lemma ldSandwichLineOnePoint
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k i : ℕ)
    (hi : i < k) :
    LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i := by
  have hgamma_nonneg : 0 ≤ gamma :=
    gamma_nonneg_of_isGood params.next strategy hgood
  have hzeta_nonneg : 0 ≤ zeta :=
    IdxPolyFamily.zeta_nonneg_of_consistentWithPoints strategy family hcons
  have hfacts : GHatFactsStatement params strategy.state family gamma zeta :=
    gHatFacts params strategy family eps delta gamma zeta
      hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le
      hgood hcons hself hbound
  exact ldSandwichLineOnePoint_ofGHatFacts params strategy eps delta gamma zeta
    hgood hgamma_le hzeta_le hdq_le family hcons hself hbound hfacts k i hi

end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/HBConsistency.lean. -/
/-!
# Section 12 pasting: H-B consistency

Aggregation theorem proving `lem:h-b-consistency` from the one-point line consistency statements.

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

/-- Aggregate one-point consistency bounds over all slice indices,
plus the distinct-tuple approximation error.

Paper reference: `lem:h-b-consistency` proof in `ld-pasting.tex`
lines 1050–1091.

Steps:
1. Expand using degree constraints to find eligible index `i`
2. Switch from independent to distinct samples (`prop:ld-dnoteq`, cost `k²/q`)
3. Union bound over `k` indices, each contributing `ν₅`
4. Total: `k·ν₅ + k²/q ≤ 44k²m(...)` -/
private lemma hBConsistency_core_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    ConsRel strategy.state
      (uniformDistribution (VerticalLineQuestion params))
      (hRestrictionToVerticalLine params
        (constructedPastedSubMeas params family k))
      (verticalLineMeasurementFamily params strategy)
      (hBConsistencyError params eps delta gamma zeta k) := by
  constructor
  have heps_nonneg : 0 ≤ eps := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (AxisParallelTestSample params.next))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy))
      haxis
  have hdelta_nonneg : 0 ≤ delta := by
    exact le_trans
      (bipartiteSSCError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      hself_good
  have hzeta_nonneg : 0 ≤ zeta := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        family.evaluatedAtNextPoint)
      hcons.pointConsistency.offDiagonalBound
  calc
    bipartiteConsError strategy.state
        (uniformDistribution (VerticalLineQuestion params))
        (hRestrictionToVerticalLine params (constructedPastedSubMeas params family k))
        (verticalLineMeasurementFamily params strategy)
      = avgOver (uniformDistribution (Point params)) (fun u =>
          qBipartiteConsDefect strategy.state
            (hRestrictionToVerticalLine params (constructedPastedSubMeas params family k) u)
            (verticalLineMeasurementFamily params strategy u)) := by
            rfl
    _ ≤ avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (distinctTupleDistribution params k) (fun xs =>
            qBipartiteConsDefect strategy.state
              (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
              (verticalLineMeasurementFamily params strategy u))) := by
            exact avgOver_mono _ _ _ (fun u =>
              hBConsistency_fixed_u_defect_le_avgOver_distinct params strategy family k u)
    _ ≤ avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (distinctTupleDistribution params k) (fun xs =>
            hBConsistencyBadMass params strategy family u xs)) := by
            exact avgOver_mono _ _ _ (fun u =>
              avgOver_distinct_pasted_defect_le_badMass params strategy family u)
    _ ≤ hBConsistencyError params eps delta gamma zeta k := by
            exact avgOver_distinct_badMass_le_hBConsistencyError_ofLinePointBounds
              params strategy family eps delta gamma zeta k hd
              heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hline

/-- Internal form of `lem:h-b-consistency` after applying
`lem:ld-sandwich-line-one-point` at each coordinate.

**Source:** The proof in `references/ldt-paper/ld-pasting.tex:1075-1109`
uses the one-point line estimates and then performs the averaging and
distinct-tuple comparison.  The paper-facing theorem `hBConsistency` below
derives the one-point estimates from the source hypotheses. -/
lemma hBConsistency_ofLinePointBounds_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    HBConsistencyStatement params strategy family
        eps delta gamma zeta k := by
  exact ⟨hBConsistency_core_of_axis_self params strategy eps delta gamma zeta
    haxis hself_good hgamma_nonneg hd family hcons hself hbound k hline⟩

lemma hBConsistency_ofLinePointBounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    HBConsistencyStatement params strategy family
        eps delta gamma zeta k := by
  have hgamma_nonneg : 0 ≤ gamma := by
    have : 0 ≤ strategy.diagonalFailureProbability := by
      unfold SymStrat.diagonalFailureProbability
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ => bipartiteConsError_nonneg strategy.state _ _ _)
    exact le_trans this hgood.diagonalLineTest
  exact hBConsistency_ofLinePointBounds_of_axis_self params strategy eps delta gamma zeta
    hgood.axisParallelTest hgood.selfConsistencyTest hgamma_nonneg hd family hcons hself
    hbound k hline

/-- `lem:h-b-consistency`, source-facing form. -/
lemma hBConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ) :
    HBConsistencyStatement params strategy family
        eps delta gamma zeta k := by
  have hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i := by
    intro i hi
    exact ldSandwichLineOnePoint params strategy eps delta gamma zeta
      hgood hgamma_le hzeta_le hdq_le family hcons hself hbound k i hi
  exact hBConsistency_ofLinePointBounds params strategy eps delta gamma zeta
    hgood hd family hcons hself hbound k hline

end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: H-A consistency

Vertical-line to point-consistency transport and completed-measurement statement for
`cor:h-a-consistency`.

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
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (eps delta gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params.next
          (_root_.LIDT.MIPStarRE.LDT.Pasting.constructedPastedSubMeas params family k))
        (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
  have hHB := _root_.LIDT.MIPStarRE.LDT.Pasting.hBConsistency params strategy eps delta gamma zeta
    hgood hgamma_le hzeta_le hdq_le hd family hcons hself hbound k
  have hgamma_nonneg : 0 ≤ gamma := by
    have : 0 ≤ strategy.diagonalFailureProbability := by
      unfold _root_.LIDT.MIPStarRE.LDT.SymStrat.diagonalFailureProbability
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ => _root_.LIDT.MIPStarRE.LDT.bipartiteConsError_nonneg strategy.state _ _ _)
    exact le_trans this hgood.diagonalLineTest
  have hzeta_nonneg : 0 ≤ zeta := by
    exact le_trans
      (_root_.LIDT.MIPStarRE.LDT.bipartiteConsError_nonneg strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        family.evaluatedAtNextPoint)
      hcons.pointConsistency.offDiagonalBound
  exact hAConsistency_submeas_core_of_axis_self params strategy family
    eps delta gamma zeta hgood.axisParallelTest hgood.selfConsistencyTest
    hgamma_nonneg hzeta_nonneg k hk_pos hHB
