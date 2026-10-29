-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.fullSliceCommutation_qSDDOp_avg_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:00:32.004065+00:00
-- url     : https://prove2.me/submissions/2e8747f9-1dec-47a7-ab8e-c1250f823823

-- Generated proof for MIPStarRE.LDT.Commutativity.fullSliceCommutation_qSDDOp_avg_eq.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_fullSliceCommutation_avg_swap_terms

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Commutativity/Transport/FullSlice/Bridges/QSDD.lean. -/
/-!
# Full-slice `qSDDOp` averaging identity

Averaging identities expanding the full-slice `qSDDOp` and proving the scalar
commutation identity `fullSliceCommutation_qSDDOp_avg_eq`.

This scalar expansion is used by the full-slice transport theorems that compare
the quartic scalar averages appearing in `commutativity-G.tex`.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Expand the averaged full-slice `qSDDOp` into the four projector terms
`BAB + ABA - BABA - ABAB`. -/
private lemma fullSliceCommutation_qSDDOp_avg_expand_full
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q =>
          qSDDOp strategy.state
            (fullSliceProductLeft params strategy family q)
            (fullSliceProductRight params strategy family q)) =
      avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q =>
          ∑ gh : FullSliceOutcome params,
            (fullSliceBABTerm params strategy family q gh +
              fullSliceABATerm params strategy family q gh -
              fullSliceBABATerm params strategy family q gh -
              fullSliceABABTerm params strategy family q gh)) := by
  apply avgOver_congr
  intro q
  unfold qSDDOp qSDDCore
  refine Finset.sum_congr rfl ?_
  intro gh _
  rcases gh with ⟨g, h⟩
  let A : MIPStarRE.Quantum.Op ι := (fullSliceFirstFactor params family q).outcome g
  let B : MIPStarRE.Quantum.Op ι := (fullSliceSecondFactor params family q).outcome h
  let LA : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) A
  let LB : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) B
  have hA_proj : A * A = A := by
    simpa [A, fullSliceFirstFactor] using (family.meas q.1).proj g
  have hB_proj : B * B = B := by
    simpa [B, fullSliceSecondFactor] using (family.meas q.2).proj h
  have hLA_herm : LAᴴ = LA := by
    let hLA_nonneg :=
      Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) ((family.meas q.1).outcome_pos g))
    exact hLA_nonneg.isHermitian.eq
  have hLB_herm : LBᴴ = LB := by
    let hLB_nonneg :=
      Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) ((family.meas q.2).outcome_pos h))
    exact hLB_nonneg.isHermitian.eq
  have hLA_proj : LA * LA = LA := by
    simpa [LA, leftTensor_mul_leftTensor] using congrArg (leftTensor (ι₂ := ι)) hA_proj
  have hLB_proj : LB * LB = LB := by
    simpa [LB, leftTensor_mul_leftTensor] using congrArg (leftTensor (ι₂ := ι)) hB_proj
  have hmain :
      (((LA * LB - LB * LA)ᴴ) * (LA * LB - LB * LA)) =
        LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB := by
    rw [show (LA * LB - LB * LA)ᴴ = LB * LA - LA * LB by
      simp [Matrix.conjTranspose_mul, hLA_herm, hLB_herm]]
    calc
      (LB * LA - LA * LB) * (LA * LB - LB * LA)
          = LB * LA * LA * LB - LB * LA * LB * LA - LA * LB * LA * LB +
              LA * LB * LB * LA := by
              noncomm_ring
      _ = LB * LA * LB - LB * LA * LB * LA - LA * LB * LA * LB + LA * LB * LA := by
            simp [mul_assoc, hLA_proj, hLB_proj]
      _ = LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB := by
            abel
  calc
    ev strategy.state
        (((fullSliceProductLeft params strategy family q).outcome (g, h) -
            (fullSliceProductRight params strategy family q).outcome (g, h))ᴴ *
          ((fullSliceProductLeft params strategy family q).outcome (g, h) -
            (fullSliceProductRight params strategy family q).outcome (g, h)))
      = ev strategy.state (((LA * LB - LB * LA)ᴴ) * (LA * LB - LB * LA)) := by
          simp [A, B, LA, LB, fullSliceProductLeft, fullSliceProductRight,
            fullSliceFirstFactor, fullSliceSecondFactor, leftOrderedProductOpFamily,
            OpFamily.leftPlacedOpFamily, orderedProductOpFamily, reversedProductOpFamily,
            leftTensor_mul_leftTensor]
    _ = ev strategy.state
          (LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB) := by
            rw [hmain]
    _ = ev strategy.state (LB * LA * LB) + ev strategy.state (LA * LB * LA) -
          ev strategy.state (LB * LA * LB * LA) -
            ev strategy.state (LA * LB * LA * LB) := by
          rw [ev_sub, ev_sub, ev_add]
    _ = ev strategy.state (leftTensor (ι₂ := ι) (B * A * B)) +
          ev strategy.state (leftTensor (ι₂ := ι) (A * B * A)) -
          ev strategy.state (leftTensor (ι₂ := ι) (B * A * B * A)) -
            ev strategy.state (leftTensor (ι₂ := ι) (A * B * A * B)) := by
          simp [LA, LB, leftTensor_mul_leftTensor, mul_assoc]
    _ = fullSliceBABTerm params strategy family q (g, h) +
          fullSliceABATerm params strategy family q (g, h) -
          fullSliceBABATerm params strategy family q (g, h) -
            fullSliceABABTerm params strategy family q (g, h) := by
          simp [fullSliceBABTerm, fullSliceABATerm,
            fullSliceBABATerm, fullSliceABABTerm, A, B]



end MIPStarRE.LDT.Commutativity

end

/- Source helpers from MIPStarRE/LDT/Commutativity/Transport/Pullback.lean. -/
/-!
# Section 11 commutativity: evaluated-slice pullback

Pullback equivalence reindexing evaluated-slice questions into their truncated
points and the underlying full-slice question, used to transport full-slice
bounds.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-- Pulling a family on `FullSliceQuestion` back along
`fullSliceQuestionOfEvaluatedSlice` preserves the averaged `sddErrorOp`. -/
lemma sddErrorOp_pullback_fullSliceQuestion_eq
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    {Outcome : Type*} [Fintype Outcome]
    (A B : IdxOpFamily (FullSliceQuestion params) Outcome (ι × ι)) :
    sddErrorOp ψ
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => A (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => B (fullSliceQuestionOfEvaluatedSlice params q)) =
    sddErrorOp ψ
      (uniformDistribution (FullSliceQuestion params))
      A B := by
  let e := evaluatedSliceQuestionEquiv params
  unfold sddErrorOp
  simpa [e, evaluatedSliceQuestionEquiv, fullSliceQuestionOfEvaluatedSlice] using
    (avgOver_uniform_equiv_snd (e := e)
      (f := fun xy : FullSliceQuestion params => qSDDOp ψ (A xy) (B xy)))




end MIPStarRE.LDT.Commutativity

end

end LIDT

open LIDT
/-!
# Full-slice `qSDDOp` averaging identity

Averaging identities expanding the full-slice `qSDDOp` and proving the scalar
commutation identity `fullSliceCommutation_qSDDOp_avg_eq`.

This scalar expansion is used by the full-slice transport theorems that compare
the quartic scalar averages appearing in `commutativity-G.tex`.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι) (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) :
    _root_.LIDT.MIPStarRE.LDT.sddErrorOp strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductLeft params strategy family
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceQuestionOfEvaluatedSlice params q))
        (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductRight params strategy family
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceQuestionOfEvaluatedSlice params q)) =
      2 * (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAAvg params strategy family -
        _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family) := by
  have hswap := _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceCommutation_avg_swap_terms params strategy family
  let D := _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params)
  rw [_root_.LIDT.MIPStarRE.LDT.Commutativity.sddErrorOp_pullback_fullSliceQuestion_eq params strategy.state
    (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductLeft params strategy family)
    (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductRight params strategy family)]
  unfold _root_.LIDT.MIPStarRE.LDT.sddErrorOp
  rw [fullSliceCommutation_qSDDOp_avg_expand_full params strategy family]
  rcases hswap with ⟨hBAB, hBABA⟩
  let BAB : _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ gh : _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceOutcome params, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABTerm params strategy family q gh
  let ABA : _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ gh : _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceOutcome params, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABATerm params strategy family q gh
  let BABA : _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ gh : _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceOutcome params, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABATerm params strategy family q gh
  let ABAB : _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ gh : _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceOutcome params, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABTerm params strategy family q gh
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver D
        (fun q =>
          ∑ gh : _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceOutcome params,
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABTerm params strategy family q gh +
              _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABATerm params strategy family q gh -
              _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABATerm params strategy family q gh -
              _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABTerm params strategy family q gh))
      = _root_.LIDT.MIPStarRE.LDT.avgOver D (fun q => (BAB q + ABA q) - (BABA q + ABAB q)) := by
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
          intro q
          dsimp [BAB, ABA, BABA, ABAB]
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
          ring
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver D (fun q => BAB q + ABA q) -
          _root_.LIDT.MIPStarRE.LDT.avgOver D (fun q => BABA q + ABAB q) := by
          simp [_root_.LIDT.MIPStarRE.LDT.avgOver, Finset.sum_sub_distrib, mul_sub]
    _ = (_root_.LIDT.MIPStarRE.LDT.avgOver D BAB + _root_.LIDT.MIPStarRE.LDT.avgOver D ABA) -
          (_root_.LIDT.MIPStarRE.LDT.avgOver D BABA + _root_.LIDT.MIPStarRE.LDT.avgOver D ABAB) := by
          rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_add]
    _ = (_root_.LIDT.MIPStarRE.LDT.avgOver D ABA + _root_.LIDT.MIPStarRE.LDT.avgOver D ABA) -
          (_root_.LIDT.MIPStarRE.LDT.avgOver D ABAB + _root_.LIDT.MIPStarRE.LDT.avgOver D ABAB) := by
          rw [hBAB, hBABA]
    _ = 2 * (_root_.LIDT.MIPStarRE.LDT.avgOver D ABA - _root_.LIDT.MIPStarRE.LDT.avgOver D ABAB) := by
          ring
    _ = 2 * (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAAvg params strategy family -
          _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family) := by
          rfl
