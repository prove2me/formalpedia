-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceCommutation_qSDDOp_avg_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:50:29.809667+00:00
-- url     : https://prove2.me/submissions/1a00b3eb-f958-41f6-9ad1-90d60fb78163

-- Generated proof for MIPStarRE.LDT.Commutativity.evaluatedSliceCommutation_qSDDOp_avg_eq.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedSliceCommutation_avg_swap_terms

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Commutativity/EvaluatedSliceCommutation/Averages.lean. -/
/-!
# Section 11 commutativity: evaluated-slice averaged expansion

Averaged evaluated-slice expansion of `qSDDOp` into the four projector terms
`BAB + ABA - BABA - ABAB`, used to reduce the commutation to per-projector
estimates.

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
/-- Expand the averaged evaluated-slice `qSDDOp` into the four projector terms
`BAB + ABA - BABA - ABAB`. -/
private lemma evaluatedSliceCommutation_qSDDOp_avg_expand
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDOp strategy.state
            (evaluatedSliceProductLeft params strategy family q)
            (evaluatedSliceProductRight params strategy family q)) =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ ab : EvaluatedSliceOutcome params,
            (evaluatedSliceBABTerm params strategy family q ab +
              evaluatedSliceABATerm params strategy family q ab -
              evaluatedSliceBABATerm params strategy family q ab -
              evaluatedSliceABABTerm params strategy family q ab)) := by
  apply avgOver_congr
  intro q
  unfold qSDDOp qSDDCore
  refine Finset.sum_congr rfl ?_
  intro ab _
  rcases ab with ⟨a, b⟩
  let A : MIPStarRE.Quantum.Op ι := (evaluatedPointFamily params family q.1).outcome a
  let B : MIPStarRE.Quantum.Op ι := (evaluatedPointFamily params family q.2).outcome b
  let LA : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) A
  let LB : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) B
  have hA_herm : Aᴴ = A := by
    simpa [A] using (evaluatedPointFamily params family q.1).outcome_hermitian a
  have hB_herm : Bᴴ = B := by
    simpa [B] using (evaluatedPointFamily params family q.2).outcome_hermitian b
  have hA_proj : A * A = A := by
    simpa [A] using evaluatedPointFamily_outcome_proj params family q.1 a
  have hB_proj : B * B = B := by
    simpa [B] using evaluatedPointFamily_outcome_proj params family q.2 b
  have hLA_herm : LAᴴ = LA := by
    let hLA_nonneg :=
      Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) ((evaluatedPointFamily params family q.1).outcome_pos a))
    exact hLA_nonneg.isHermitian.eq
  have hLB_herm : LBᴴ = LB := by
    let hLB_nonneg :=
      Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) ((evaluatedPointFamily params family q.2).outcome_pos b))
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
          = LB * LA * LA * LB - LB * LA * LB * LA - LA * LB * LA * LB + LA * LB * LB * LA := by
              noncomm_ring
      _ = LB * LA * LB - LB * LA * LB * LA - LA * LB * LA * LB + LA * LB * LA := by
            simp [mul_assoc, hLA_proj, hLB_proj]
      _ = LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB := by
            abel
  calc
    ev strategy.state
        (((evaluatedSliceProductLeft params strategy family q).outcome (a, b) -
            (evaluatedSliceProductRight params strategy family q).outcome (a, b))ᴴ *
          ((evaluatedSliceProductLeft params strategy family q).outcome (a, b) -
            (evaluatedSliceProductRight params strategy family q).outcome (a, b)))
      = ev strategy.state (((LA * LB - LB * LA)ᴴ) * (LA * LB - LB * LA)) := by
          simp [A, B, LA, LB, evaluatedSliceProductLeft, evaluatedSliceProductRight,
            evaluatedSliceFirstFactor, evaluatedSliceSecondFactor, evaluatedPointFamily,
            leftOrderedProductOpFamily, OpFamily.leftPlacedOpFamily,
            orderedProductOpFamily, reversedProductOpFamily, leftTensor_mul_leftTensor]
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
    _ = evaluatedSliceBABTerm params strategy family q (a, b) +
          evaluatedSliceABATerm params strategy family q (a, b) -
          evaluatedSliceBABATerm params strategy family q (a, b) -
            evaluatedSliceABABTerm params strategy family q (a, b) := by
          simp [evaluatedSliceBABTerm, evaluatedSliceABATerm,
            evaluatedSliceBABATerm, evaluatedSliceABABTerm, A, B]






end MIPStarRE.LDT.Commutativity

end

end LIDT

open LIDT
/-!
# Section 11 commutativity: evaluated-slice averaged expansion

Averaged evaluated-slice expansion of `qSDDOp` into the four projector terms
`BAB + ABA - BABA - ABAB`, used to reduce the commutation to per-projector
estimates.

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
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceProductLeft params strategy family)
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceProductRight params strategy family) =
      2 *
        (_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
            (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
              _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABATerm params strategy family q ab) -
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
            (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
              _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab)) := by
  have hswap :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceCommutation_avg_swap_terms params strategy family
  unfold _root_.LIDT.MIPStarRE.LDT.sddErrorOp
  rw [evaluatedSliceCommutation_qSDDOp_avg_expand]
  rcases hswap with ⟨hBAB, hBABA⟩
  let sf : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABTerm params strategy family q ab
  let sg : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABATerm params strategy family q ab
  let sh : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABATerm params strategy family q ab
  let sk : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab
  have hpoint :
      ∀ q,
        (∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABTerm params strategy family q ab +
              _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABATerm params strategy family q ab -
              _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABATerm params strategy family q ab -
              _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab)) =
          sf q + sg q - sh q - sk q := by
    intro q
    dsimp [sf, sg, sh, sk]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hsplit :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (fun q => sf q + sg q - sh q - sk q) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)) sf +
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)) sg -
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)) sh -
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)) sk := by
    unfold _root_.LIDT.MIPStarRE.LDT.avgOver
    have hmul :
        ∀ q,
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)).weight q *
              (sf q + sg q - sh q - sk q) =
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)).weight q * sf q +
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)).weight q * sg q -
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)).weight q * sh q -
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)).weight q * sk q := by
      intro q
      ring
    simp_rw [hmul, sub_eq_add_neg]
    repeat rw [Finset.sum_add_distrib]
    simp_rw [Finset.sum_neg_distrib]
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (fun q =>
          ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABTerm params strategy family q ab +
              _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABATerm params strategy family q ab -
              _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABATerm params strategy family q ab -
              _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab))
      = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABTerm params strategy family q ab) +
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABATerm params strategy family q ab) -
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABATerm params strategy family q ab) -
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab) := by
            calc
              _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
                  (fun q =>
                    ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
                      (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABTerm params strategy family q ab +
                        _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABATerm params strategy family q ab -
                        _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABATerm params strategy family q ab -
                        _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab))
                = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
                    (fun q => sf q + sg q - sh q - sk q) := by
                      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
                      intro q
                      exact hpoint q
              _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)) sf +
                  _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)) sg -
                  _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)) sh -
                  _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)) sk := hsplit
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABATerm params strategy family q ab) +
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABATerm params strategy family q ab) -
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab) -
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab) := by
            rw [hBAB, hBABA]
    _ = 2 *
          (_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
              (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
                _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABATerm params strategy family q ab) -
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
              (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
                _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab)) := by
            ring
