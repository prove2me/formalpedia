-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftLift
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:09:08.615605+00:00
-- url     : https://prove2.me/submissions/bec74651-3158-421c-93f6-d482d62ef3af

-- Generated proof for MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftLift.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_subMeas_sum_adjoint_mul_le_one
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

end LIDT

open LIDT
/-!
# Section 12 pasting: half-sandwich lifting constructions

This module contains the reindexing equivalences and lifted operator families
which transport an `r`-step half-sandwich move comparison to the corresponding
`r+1`-step comparison.

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


/-! ## Lifting families for the half-sandwich chain

Lifting constructions: swapped-front equivalences, `splitSuccLiftFamily`,
`prefixSecondSliceLeftFamily`, `secondSliceLiftFamily`, and the
`moveChainLift` construction that lifts an `r`-step chain to `r+1`.
-/

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) (r : ℕ)
    (A B : _root_.LIDT.MIPStarRE.LDT.IdxOpFamily
      (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r)
      (ι × ι))
    (δ : _root_.LIDT.MIPStarRE.LDT.Error)
    (hAB : _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params r))
      A B
      δ) :
    _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftFamily params family r A)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftFamily params family r B)
      δ := by
  have hABfst :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          ((_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.PointTuple params r) × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
        (fun q => A q.1)
        (fun q => B q.1)
        δ :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.sddOpRel_uniform_fst ψbi A B δ hAB
  have hABtriple :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r))
        (fun q => A (q.1, q.2.2))
        (fun q => B (q.1, q.2.2))
        δ :=
    (_root_.LIDT.MIPStarRE.LDT.Pasting.sddOpRel_uniform_equiv (_root_.LIDT.MIPStarRE.LDT.Pasting.splitQuestionEquiv params r) ψbi
      (fun q => A q.1)
      (fun q => B q.1)
      δ).1 hABfst
  let C : (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r) →
      (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r) → _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params →
      _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q _ gy => _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome gy)
  have hC :
      ∀ q a,
        ∑ gy : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, (C q a gy)ᴴ * C q a gy ≤ 1 := by
    intro q a
    calc
      ∑ gy : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params, (C q a gy)ᴴ * C q a gy
        = ∑ gy : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome gy)ᴴ) *
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome gy) := by
                  refine Finset.sum_congr rfl ?_
                  intro gy _
                  rw [show
                      (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                        ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome gy))ᴴ =
                        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                          (show _root_.LIDT.MIPStarRE.Quantum.Op ι from
                            ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome gy)ᴴ) by
                    simpa [_root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor] using
                      (_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome gy)
                        (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))]
                  simp [C, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor]
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            (∑ gy : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
              (((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome gy)ᴴ) *
                (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).outcome gy) := by
                  rw [← _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ]
      _ ≤ _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := by
            simpa using
              _root_.LIDT.MIPStarRE.LDT.opTensor_mono_left (ι₂ := ι) (B := (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))
                (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.subMeas_sum_adjoint_mul_le_one
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family q.2.1).toSubMeas))
                (show (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ≤ 1 by exact zero_le_one)
      _ = 1 := by simp [_root_.LIDT.MIPStarRE.LDT.leftTensor]
  let rawSource : _root_.LIDT.MIPStarRE.LDT.IdxOpFamily (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r)
      ((_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r) × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (A (q.1, q.2.2)).outcome ag.1
        total := ∑ ag : (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r) × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
          C q ag.1 ag.2 * (A (q.1, q.2.2)).outcome ag.1 }
  let rawTarget : _root_.LIDT.MIPStarRE.LDT.IdxOpFamily (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r)
      ((_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r) × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params) (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (B (q.1, q.2.2)).outcome ag.1
        total := ∑ ag : (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params r) × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params,
          C q ag.1 ag.2 * (B (q.1, q.2.2)).outcome ag.1 }
  have hcab :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r))
      (fun q => A (q.1, q.2.2))
      (fun q => B (q.1, q.2.2))
      C δ hABtriple hC
  have hreindex := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_reindex (_root_.LIDT.MIPStarRE.LDT.Pasting.prefixTripleOutcomeEquiv params r)
    ψbi
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r))
    rawSource rawTarget δ hcab
  let reindexedSource : _root_.LIDT.MIPStarRE.LDT.IdxOpFamily (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params ×
      _root_.LIDT.MIPStarRE.LDT.PointTuple params r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveO params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawSource q).outcome ((_root_.LIDT.MIPStarRE.LDT.Pasting.prefixTripleOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget : _root_.LIDT.MIPStarRE.LDT.IdxOpFamily (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params × _root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params ×
      _root_.LIDT.MIPStarRE.LDT.PointTuple params r)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveO params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawTarget q).outcome ((_root_.LIDT.MIPStarRE.LDT.Pasting.prefixTripleOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome ψbi
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.MoveQ params r))
    reindexedSource reindexedTarget
    (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftFamily params family r A)
    (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftFamily params family r B)
    δ
    (fun q ogs => by
      simp [reindexedSource, rawSource, _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftFamily,
        _root_.LIDT.MIPStarRE.LDT.Pasting.prefixTripleOutcomeEquiv, C])
    (fun q ogs => by
      simp [reindexedTarget, rawTarget, _root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwich_prefixSecondSliceLeftFamily,
        _root_.LIDT.MIPStarRE.LDT.Pasting.prefixTripleOutcomeEquiv, C])
    hreindex
