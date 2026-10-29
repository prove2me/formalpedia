-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepMid_toTarget
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:17:05.836734+00:00
-- url     : https://prove2.me/submissions/369d6300-6493-4229-a154-23e0fdd7b8cd

-- Generated proof for MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepMid_toTarget.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_gHatPairPrefix_sum_adjoint_mul_le_one
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_gHatReverseHalfProduct_sum_adjoint_mul_le_one
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_leftTensor_rightTensor_sum_adjoint_mul_le_one
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_sddOpRel_uniform_equiv

open scoped _root_.Matrix

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























/-! ### Base cases and consistency lifts -/

lemma gHatSelfConsistency_sddOpRel
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params))
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family))
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family))
      (gHatSelfConsistencyError zeta) := by
  rcases hsc with ⟨h⟩
  exact ⟨by
    simpa [sddError, sddErrorOp, qSDD, qSDDOp, qSDDCore,
      IdxSubMeas.toIdxOpFamily, SubMeas.toOpFamily] using h⟩

lemma sddOpRel_uniform_fst
    {α β Outcome : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A B : IdxOpFamily α Outcome (ι × ι))
    (δ : Error) :
    SDDOpRel ψ (uniformDistribution α) A B δ →
      SDDOpRel ψ (uniformDistribution (α × β))
        (fun ab => A ab.1)
        (fun ab => B ab.1)
        δ := by
  intro ⟨h⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver (uniformDistribution (α × β)) (fun ab => qSDDOp ψ (A ab.1) (B ab.1))
      = avgOver (uniformDistribution α) (fun a => qSDDOp ψ (A a) (B a)) := by
          exact avgOver_uniform_fst (fun a => qSDDOp ψ (A a) (B a))
    _ ≤ δ := h



/-! ### Slice-front equivalences -/



/-! ### Question/outcome equivalences -/







/-! ### Split-successor and move-tail equivalences -/













/-! ### Move-step and source families -/









/-! ### Move-source splitting lemmas -/





/-! ### One-element tuple equivalences -/









/-! ### Outcome slice-front equivalences -/



end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/Setup/StepLemmas/Move.lean. -/
/-!
# Section 12 pasting: commute G half-sandwich move lemmas

This module contains the move-chain lemmas for the half-sandwich commutation
chain.  The split reindexing lemmas and the two-term base case are kept in
`StepLemmas.Split`.

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

lemma gHatSelfConsistency_sddOpRel_quadThird
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error) (r : ℕ)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params ×
        SliceQuestion params × PointTuple params r))
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.2.2.1)
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.2.2.1)
      (gHatSelfConsistencyError zeta) := by
  have hfst :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params ×
          (SliceQuestion params × SliceQuestion params × PointTuple params r)))
        (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.1)
        (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.1)
        (gHatSelfConsistencyError zeta) :=
    sddOpRel_uniform_fst ψbi
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family))
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family))
      (gHatSelfConsistencyError zeta)
      (gHatSelfConsistency_sddOpRel params ψbi family zeta hsc)
  simpa [thirdSliceFrontEquiv] using
    (sddOpRel_uniform_equiv (thirdSliceFrontEquiv params r).symm ψbi
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.1)
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.1)
      (gHatSelfConsistencyError zeta)).1 hfst








end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: commute G half-sandwich move lemmas

This module contains the move-chain lemmas for the half-sandwich commutation
chain.  The split reindexing lemmas and the two-term base case are kept in
`StepLemmas.Split`.

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
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (zeta : _root_.LIDT.MIPStarRE.LDT.Error) (r : ℕ)
    (hsc : _root_.LIDT.MIPStarRE.LDT.SDDRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyLeftFamily params family)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyRightFamily params family)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta)) :
    _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
        (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params r))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepMidFamily params family r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepTargetFamily params family r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta) := by
  let Q := _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params r
  let Aop : _root_.LIDT.MIPStarRE.LDT.IdxOpFamily Q (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) (ι × ι) :=
    fun q => (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.toIdxOpFamily (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyLeftFamily params family)) q.2.2.1
  let Bop : _root_.LIDT.MIPStarRE.LDT.IdxOpFamily Q (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) (ι × ι) :=
    fun q => (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.toIdxOpFamily (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyRightFamily params family)) q.2.2.1
  let C : Q → _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params → ((_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) ×
      _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r) →
      _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q _ ag =>
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
          (((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ag.1.1) *
            ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome ag.1.2)) *
        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ag.2)
  have hAB :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Q)
        Aop Bop
        (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta) :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistency_sddOpRel_quadThird params ψbi family zeta r hsc
  have hC :
      ∀ q a,
        ∑ ag : ((_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r),
            (C q a ag)ᴴ * C q a ag ≤ 1 := by
    intro q a
    let pairProd : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params → _root_.LIDT.MIPStarRE.Quantum.Op ι :=
      fun og => ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome og.1) *
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome og.2)
    let tailOp : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r → _root_.LIDT.MIPStarRE.Quantum.Op ι :=
      fun gs => _root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 gs
    have hpair :
        ∑ og : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
            (pairProd og)ᴴ * pairProd og ≤ 1 := by
      simpa [pairProd] using
        _root_.LIDT.MIPStarRE.LDT.Pasting.gHatPairPrefix_sum_adjoint_mul_le_one params family (q.1, q.2.1)
    have htail :
        ∑ gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r,
            (tailOp gs)ᴴ * tailOp gs ≤ 1 := by
      simpa [tailOp] using
        _root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProduct_sum_adjoint_mul_le_one params family r q.2.2.2
    simpa [C, pairProd, tailOp] using
      (_root_.LIDT.MIPStarRE.LDT.Pasting.leftTensor_rightTensor_sum_adjoint_mul_le_one
        (ι := ι) (prefixOp := pairProd) (tailOp := tailOp) hpair htail)
  let rawSource : _root_.LIDT.MIPStarRE.LDT.IdxOpFamily Q
      (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × ((_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r))
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (Aop q).outcome ag.1
        total := ∑ ag : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × ((_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) ×
            _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r),
          C q ag.1 ag.2 * (Aop q).outcome ag.1 }
  let rawTarget : _root_.LIDT.MIPStarRE.LDT.IdxOpFamily Q
      (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × ((_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r))
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (Bop q).outcome ag.1
        total := ∑ ag : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × ((_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) ×
            _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r),
          C q ag.1 ag.2 * (Bop q).outcome ag.1 }
  have hcab :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Q) Aop Bop C (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta) hAB hC
  have hreindex := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_reindex (_root_.LIDT.MIPStarRE.LDT.Pasting.thirdSliceFrontOutcomeEquiv params r)
    ψbi (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Q) rawSource rawTarget (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta) hcab
  let reindexedSource : _root_.LIDT.MIPStarRE.LDT.IdxOpFamily Q
      (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params ×
          _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawSource q).outcome ((_root_.LIDT.MIPStarRE.LDT.Pasting.thirdSliceFrontOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget : _root_.LIDT.MIPStarRE.LDT.IdxOpFamily Q
      (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params ×
          _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawTarget q).outcome ((_root_.LIDT.MIPStarRE.LDT.Pasting.thirdSliceFrontOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome ψbi
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Q)
    reindexedSource reindexedTarget
    (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepMidFamily params family r)
    (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepTargetFamily params family r)
    (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatSelfConsistencyError zeta)
    (fun q ogs => by
      let A := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
      let B := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let G := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1
      let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2
      have hAop : (Aop q).outcome ogs.2.2.1 = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G := by
        rfl
      have hcomm : _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G =
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T := by
        rw [_root_.LIDT.MIPStarRE.LDT.rightTensor_mul_leftTensor_eq_opTensor, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
      calc
        (reindexedSource q).outcome ogs =
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A * B) *
              (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T * (Aop q).outcome ogs.2.2.1) := by
              simp [reindexedSource, rawSource, _root_.LIDT.MIPStarRE.LDT.Pasting.thirdSliceFrontOutcomeEquiv, C, A, B, T, mul_assoc]
        _ =
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A * B) *
              (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G) := by
              rw [hAop]
        _ =
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A * B) *
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T) := by
              rw [hcomm]
        _ = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs := by
              calc
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A * B) *
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T)
                  =
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A * B) * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G) *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T := by
                      simp [mul_assoc]
                _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A * B) * G) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T := by
                      rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor]
                _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A * (B * G)) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T := by
                      simp [mul_assoc]
                _ = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs := by
                      simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepMidFamily, A, B, G, T,
                        _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor, mul_assoc]
    )
    (fun q ogs => by
      let A := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.1).outcome ogs.1
      let B := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let G := (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1
      let T := _root_.LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2
      have hBop : (Bop q).outcome ogs.2.2.1 = _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) G := by
        rfl
      calc
        (reindexedTarget q).outcome ogs
          = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A * B) *
              (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T * (Bop q).outcome ogs.2.2.1) := by
                simp [reindexedTarget, rawTarget, _root_.LIDT.MIPStarRE.LDT.Pasting.thirdSliceFrontOutcomeEquiv, C, A, B, T,
                    mul_assoc]
        _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A * B) *
              (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) G) := by
                rw [hBop]
        _ = (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepTargetFamily params family r q).outcome ogs := by
              symm
              calc
                (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepTargetFamily params family r q).outcome ogs
                  = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                      (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) G) := by
                        simp [_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_moveStepTargetFamily, A, B, G, T, mul_assoc]
                _ =
                    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (T * G) := by
                      rw [_root_.LIDT.MIPStarRE.LDT.rightTensor_mul_rightTensor]
                _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A * B) * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (T * G) := by
                      rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor]
                _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A * B) *
                      (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) G) := by
                        rw [_root_.LIDT.MIPStarRE.LDT.rightTensor_mul_rightTensor]
    )
    hreindex
