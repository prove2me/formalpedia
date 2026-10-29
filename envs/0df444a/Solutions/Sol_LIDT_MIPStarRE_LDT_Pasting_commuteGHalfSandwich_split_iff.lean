-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_split_iff
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:09:08.385757+00:00
-- url     : https://prove2.me/submissions/312d0498-6965-4eee-83f1-3bc89a28a81f

-- Generated proof for MIPStarRE.LDT.Pasting.commuteGHalfSandwich_split_iff.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_sddOpRel_congr_outcome
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_sddOpRel_reindex
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_sddOpRel_uniform_equiv

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

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/Setup/Definitions.lean. -/
/-!
# Section 12 pasting: commute G half-sandwich setup — definitions

Tuple equivalences, operator definitions, and family constructions for the half-sandwich
commutation chain. This module contains all `def`/`noncomputable def` declarations and small
helper lemmas used by the sum-bound and step-commutation submodules.

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

/-! ### Sandwich-chain comparison lemmas

These lemmas capture the infrastructure needed for the `lem:commute-g-half-sandwich`
through `cor:h-a-consistency` chain in `ld-pasting.tex` §9.3.

The n-step SDDOpRel composition lemma (`sddOpRel_chain`) lives in
`MIPStarRE.LDT.Preliminaries.CompletionTransfer` alongside `sddOpRel_triangle`,
since it is a general-purpose result used by multiple chapters. -/













lemma gHatHalfSandwichLeft_split_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params (k + 1))
    (gs : GHatTupleOutcome params (k + 1)) :
    (gHatHalfSandwichLeft params family (k + 1) xs).outcome gs =
      (headTailOrderedFamily params family k ((pointTupleConsEquiv params k) xs)).outcome
        ((gHatTupleOutcomeConsEquiv' params k) gs) := by
  simp [gHatHalfSandwichLeft, headTailOrderedFamily,
    pointTupleConsEquiv, gHatTupleOutcomeConsEquiv',
    gHatHalfProductOutcomeOperator, OpFamily.leftPlacedOpFamily,
    leftTensor_mul_leftTensor]



lemma gHatHalfSandwichRight_split_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params (k + 1))
    (gs : GHatTupleOutcome params (k + 1)) :
    (gHatHalfSandwichRight params family (k + 1) xs).outcome gs =
      (headTailRotatedFamily params family k ((pointTupleConsEquiv params k) xs)).outcome
        ((gHatTupleOutcomeConsEquiv' params k) gs) := by
  simp [gHatHalfSandwichRight, headTailRotatedFamily,
    pointTupleConsEquiv, gHatTupleOutcomeConsEquiv',
    gHatRotatedHalfProductOutcomeOperator, OpFamily.leftPlacedOpFamily,
    leftTensor_mul_leftTensor]





/-! ### Base cases and consistency lifts -/







/-! ### Slice-front equivalences -/



/-! ### Question/outcome equivalences -/







/-! ### Split-successor and move-tail equivalences -/













/-! ### Move-step and source families -/









/-! ### Move-source splitting lemmas -/





/-! ### One-element tuple equivalences -/









/-! ### Outcome slice-front equivalences -/



end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/Setup/StepLemmas/Split.lean. -/
/-!
# Section 12 pasting: commute G half-sandwich split lemmas

This module contains the split reindexing lemmas and the two-term base case for
the half-sandwich commutation chain.

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

private lemma gHatHalfSandwichLeft_split_outcome_cons
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (q : SliceQuestion params × PointTuple params k)
    (ogs : GHatOutcome params × GHatTupleOutcome params k) :
    (gHatHalfSandwichLeft params family (k + 1) ((pointTupleConsEquiv params k).symm q)).outcome
        ((gHatTupleOutcomeConsEquiv' params k).symm ogs) =
      (headTailOrderedFamily params family k q).outcome ogs := by
  have hq : (q.1, pointTupleTail (Fin.cons q.1 q.2)) = q := by
    cases q
    congr
  have hogs : (ogs.1, gHatTupleOutcomeTail (Fin.cons ogs.1 ogs.2)) = ogs := by
    cases ogs
    congr
  simpa [pointTupleConsEquiv, gHatTupleOutcomeConsEquiv', hq, hogs] using
    gHatHalfSandwichLeft_split_outcome params family k
      ((pointTupleConsEquiv params k).symm q)
      ((gHatTupleOutcomeConsEquiv' params k).symm ogs)

private lemma gHatHalfSandwichRight_split_outcome_cons
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (q : SliceQuestion params × PointTuple params k)
    (ogs : GHatOutcome params × GHatTupleOutcome params k) :
    (gHatHalfSandwichRight params family (k + 1) ((pointTupleConsEquiv params k).symm q)).outcome
        ((gHatTupleOutcomeConsEquiv' params k).symm ogs) =
      (headTailRotatedFamily params family k q).outcome ogs := by
  have hq : (q.1, pointTupleTail (Fin.cons q.1 q.2)) = q := by
    cases q
    congr
  have hogs : (ogs.1, gHatTupleOutcomeTail (Fin.cons ogs.1 ogs.2)) = ogs := by
    cases ogs
    congr
  simpa [pointTupleConsEquiv, gHatTupleOutcomeConsEquiv', hq, hogs] using
    gHatHalfSandwichRight_split_outcome params family k
      ((pointTupleConsEquiv params k).symm q)
      ((gHatTupleOutcomeConsEquiv' params k).symm ogs)











end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: commute G half-sandwich split lemmas

This module contains the split reindexing lemmas and the two-term base case for
the half-sandwich commutation chain.

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
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) (k : ℕ) (δ : _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params (k + 1)))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfSandwichLeft params family (k + 1))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfSandwichRight params family (k + 1))
      δ ↔
    _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params k))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.headTailOrderedFamily params family k)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.headTailRotatedFamily params family k)
      δ := by
  constructor
  · intro h
    have hq :=
      (_root_.LIDT.MIPStarRE.LDT.Pasting.sddOpRel_uniform_equiv (_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleConsEquiv params k) ψbi
        (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfSandwichLeft params family (k + 1))
        (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfSandwichRight params family (k + 1)) δ).1 h
    have ho := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_reindex (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeConsEquiv' params k)
      ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params k))
      (fun q => _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfSandwichLeft params family (k + 1) ((_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleConsEquiv params k).symm q))
      (fun q => _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfSandwichRight params family (k + 1) ((_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleConsEquiv params k).symm q))
      δ hq
    exact _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params k))
      _ _
      (_root_.LIDT.MIPStarRE.LDT.Pasting.headTailOrderedFamily params family k)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.headTailRotatedFamily params family k)
      δ
      (fun q ogs => by
        exact gHatHalfSandwichLeft_split_outcome_cons params family k q ogs)
      (fun q ogs => by
        exact gHatHalfSandwichRight_split_outcome_cons params family k q ogs)
      ho
  · intro h
    have ho := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_reindex (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeConsEquiv' params k).symm
      ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params k))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.headTailOrderedFamily params family k)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.headTailRotatedFamily params family k)
      δ h
    have hq := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params k))
      _ _
      (fun q => _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfSandwichLeft params family (k + 1) ((_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleConsEquiv params k).symm q))
      (fun q => _root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfSandwichRight params family (k + 1) ((_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleConsEquiv params k).symm q))
      δ
      (fun q gs => by
        simpa using (gHatHalfSandwichLeft_split_outcome_cons params family k q
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeConsEquiv' params k) gs)).symm)
      (fun q gs => by
        simpa using (gHatHalfSandwichRight_split_outcome_cons params family k q
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleOutcomeConsEquiv' params k) gs)).symm)
      ho
    exact (_root_.LIDT.MIPStarRE.LDT.Pasting.sddOpRel_uniform_equiv (_root_.LIDT.MIPStarRE.LDT.Pasting.pointTupleConsEquiv params k) ψbi
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfSandwichLeft params family (k + 1))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatHalfSandwichRight params family (k + 1)) δ).2 hq
