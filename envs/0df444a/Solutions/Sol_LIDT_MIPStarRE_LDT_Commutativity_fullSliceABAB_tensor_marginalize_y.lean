-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAB_tensor_marginalize_y
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:05:52.329415+00:00
-- url     : https://prove2.me/submissions/c51965b8-3470-4660-93f9-76ffd1955800

-- Generated proof for MIPStarRE.LDT.Commutativity.fullSliceABAB_tensor_marginalize_y.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_avg_postprocess_sandwichTensor_eq_diag_add_collision
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_fullSliceABAByCollisionFactored_nonneg

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Commutativity/Transport/FullSlice/Machinery/Marginalization/Core.lean. -/
/-!
# Full-slice tensor marginalization core

Collision residuals, postprocessing expansions, and tensor marginalization
core bounds for the `BABA` and `ABAB` full-slice tensor averages.

Ex-private definitions are tensor-form machinery per architecture decision
#713; downstream code should use the scalar public API exposed by the
full-slice transport theorems.

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







/-- The Schwartz-Zippel/PSD bound for the y-marginalization collision residual.

This is the proved hard estimate used by the staged y-marginalization tensor
lemma below; the postprocessing expansion identifies the data-ordered evaluated
tensor-average difference with `fullSliceABAByCollisionFactored`. -/
private lemma fullSliceABAByCollisionFactored_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized)
    (u : Point params) (xy : FullSliceQuestion params) :
    fullSliceABAByCollisionFactored params strategy family u xy ≤
      (params.m * params.d : Error) / params.q := by
  let A : SubMeas (Fq params) ι :=
    evaluateAt params u ((family.meas xy.1).toSubMeas)
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  simpa [fullSliceABAByCollisionFactored, A, B] using
    MIPStarRE.LDT.Preliminaries.polynomialCollision_sandwichTensor_le_mdq
      params strategy.state hnorm A B B



/-- Averaged y-collision bound in the form consumed by
`fullSliceABAB_tensor_marginalize_y`. This is the y-side analogue of
`fullSliceBABA_tensor_marginalize_x_collision_bound`. -/
lemma fullSliceABAB_tensor_marginalize_y_collision_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized) :
    avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2) ≤
      (params.m * params.d : Error) / params.q := by
  let δ : Error := (params.m * params.d : Error) / params.q
  exact avgOver_uniform_le_const
    (α := Point params × FullSliceQuestion params)
    (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2)
    δ
    (by
      intro ux
      simpa [δ] using
        fullSliceABAByCollisionFactored_le_mdq params strategy family hnorm ux.1 ux.2)



















end MIPStarRE.LDT.Commutativity

end

/- Source helpers from MIPStarRE/LDT/Commutativity/Transport/FullSlice/Machinery/Marginalization/Y.lean. -/
/-!
# Full-slice y-marginalization endpoint

This module contains the y-side evaluated tensor marginalization block for the
`ABAB` full-slice tensor average.  It imports the collision and postprocessing
machinery from `Machinery.Marginalization.Core` and preserves the original
public marginalization theorem.

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





/-- Pointwise form of `evaluatedSliceABABtensorAvg_eq_yData`, after expanding the
question reindexing equivalence. -/
private lemma evaluatedSliceABABtensorYData_point
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (u : Point params) (x y : Fq params) (v : Point params) :
    (∑ ab : EvaluatedSliceOutcome params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            ((evaluatedSliceFirstFactor params family
                (appendPoint params u x, appendPoint params v y)).outcome ab.1 *
              (evaluatedSliceSecondFactor params family
                (appendPoint params u x, appendPoint params v y)).outcome ab.2 *
              (evaluatedSliceFirstFactor params family
                (appendPoint params u x, appendPoint params v y)).outcome ab.1) *
          rightTensor (ι₁ := ι)
            ((evaluatedSliceSecondFactor params family
              (appendPoint params u x, appendPoint params v y)).outcome ab.2))) =
      evaluatedSliceABABtensorYDataTerm (ι := ι) params strategy family (((u, (x, y)), v)) := by
  unfold evaluatedSliceABABtensorYDataTerm
  dsimp [evaluatedSliceFirstFactor, evaluatedSliceSecondFactor, evaluatedPointFamily,
    IdxPolyFamily.evaluatedAtNextPoint]
  simp only [truncatePoint_appendPoint, pointHeight_appendPoint]
  calc
    (∑ ab : Fq params × Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            ((evaluateAt params u ((family.meas x).toSubMeas)).outcome ab.1 *
              (evaluateAt params v ((family.meas y).toSubMeas)).outcome ab.2 *
              (evaluateAt params u ((family.meas x).toSubMeas)).outcome ab.1) *
          rightTensor (ι₁ := ι)
            ((evaluateAt params v ((family.meas y).toSubMeas)).outcome ab.2)))
      = ∑ a : Fq params, ∑ b : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((evaluateAt params u ((family.meas x).toSubMeas)).outcome a *
                (evaluateAt params v ((family.meas y).toSubMeas)).outcome b *
                (evaluateAt params u ((family.meas x).toSubMeas)).outcome a) *
            rightTensor (ι₁ := ι)
              ((evaluateAt params v ((family.meas y).toSubMeas)).outcome b)) := by
          exact Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((evaluateAt params u ((family.meas x).toSubMeas)).outcome a *
                    (evaluateAt params v ((family.meas y).toSubMeas)).outcome b *
                    (evaluateAt params u ((family.meas x).toSubMeas)).outcome a) *
                rightTensor (ι₁ := ι)
                  ((evaluateAt params v ((family.meas y).toSubMeas)).outcome b)))
    _ = ∑ b : Fq params, ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((evaluateAt params u ((family.meas x).toSubMeas)).outcome a *
                (evaluateAt params v ((family.meas y).toSubMeas)).outcome b *
                (evaluateAt params u ((family.meas x).toSubMeas)).outcome a) *
            rightTensor (ι₁ := ι)
              ((evaluateAt params v ((family.meas y).toSubMeas)).outcome b)) := by
          rw [Finset.sum_comm]

/-- Reindex the evaluated `ABA ⊗ B` tensor average by `((u, (x, y)), v)`
and write the outcome sum in the y-first order used by the generic postprocessing
expansion. -/
private lemma evaluatedSliceABABtensorAvg_eq_yData
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    evaluatedSliceABABtensorAvg params strategy family =
      evaluatedSliceABABtensorYDataAvg params strategy family := by
  classical
  unfold evaluatedSliceABABtensorAvg evaluatedSliceABABtensorYDataAvg
  let e := evaluatedSliceQuestionYDataEquiv params
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ ab : EvaluatedSliceOutcome params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((evaluatedSliceFirstFactor params family q).outcome ab.1 *
                    (evaluatedSliceSecondFactor params family q).outcome ab.2 *
                    (evaluatedSliceFirstFactor params family q).outcome ab.1) *
                rightTensor (ι₁ := ι)
                  ((evaluatedSliceSecondFactor params family q).outcome ab.2)))
      = avgOver (uniformDistribution ((Point params × FullSliceQuestion params) × Point params))
          (fun r =>
            ∑ ab : EvaluatedSliceOutcome params,
              ev strategy.state
                (leftTensor (ι₂ := ι)
                    ((evaluatedSliceFirstFactor params family (e.symm r)).outcome ab.1 *
                      (evaluatedSliceSecondFactor params family (e.symm r)).outcome ab.2 *
                      (evaluatedSliceFirstFactor params family (e.symm r)).outcome ab.1) *
                  rightTensor (ι₁ := ι)
                    ((evaluatedSliceSecondFactor params family (e.symm r)).outcome ab.2))) := by
            exact avgOver_uniform_equiv e _
    _ = avgOver (uniformDistribution ((Point params × FullSliceQuestion params) × Point params))
        (fun r => evaluatedSliceABABtensorYDataTerm (ι := ι) params strategy family r) := by
          apply avgOver_congr
          rintro ⟨⟨u, ⟨x, y⟩⟩, v⟩
          simpa [e, evaluatedSliceQuestionYDataEquiv] using
            evaluatedSliceABABtensorYData_point params strategy family u x y v

/-- Exact y-side postprocessing identity: the fully evaluated `ABA ⊗ B` tensor
average is the x-evaluated/y-full tensor average plus the y-collision residual. -/
private lemma evaluatedSliceABABtensor_yEvaluation_eq_xFull_add_collision
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    evaluatedSliceABABtensorAvg params strategy family =
      xEvaluatedFullSliceABABtensorAvg params strategy family +
        avgOver (uniformDistribution (Point params × FullSliceQuestion params))
          (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2) := by
  classical
  let 𝒟 : Distribution (Point params × FullSliceQuestion params) :=
    uniformDistribution (Point params × FullSliceQuestion params)
  let diag : Point params × FullSliceQuestion params → Error := fun ux =>
    let A : SubMeas (Fq params) ι :=
      evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
    let B : SubMeas (Polynomial params) ι := (family.meas ux.2.2).toSubMeas
    ∑ h : Polynomial params, ∑ a : Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι) (A.outcome a * B.outcome h * A.outcome a) *
          rightTensor (ι₁ := ι) (B.outcome h))
  have hdata := evaluatedSliceABABtensorAvg_eq_yData params strategy family
  have hpoint (ux : Point params × FullSliceQuestion params) :
      avgOver (uniformDistribution (Point params))
        (fun v =>
          let A : SubMeas (Fq params) ι :=
            evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
          let B : SubMeas (Fq params) ι :=
            evaluateAt params v ((family.meas ux.2.2).toSubMeas)
          ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b * A.outcome a) *
                rightTensor (ι₁ := ι) (B.outcome b))) =
        diag ux + fullSliceABAByCollisionFactored params strategy family ux.1 ux.2 := by
    let A : SubMeas (Fq params) ι :=
      evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
    let B : SubMeas (Polynomial params) ι := (family.meas ux.2.2).toSubMeas
    simpa [diag, fullSliceABAByCollisionFactored, A, B, evaluateAt] using
      (avg_postprocess_sandwichTensor_eq_diag_add_collision
        (ψ := strategy.state) (A := B) (B := A)
        (eval := fun v : Point params => fun h : Polynomial params => h v))
  have hdiag : avgOver 𝒟 diag = xEvaluatedFullSliceABABtensorAvg params strategy family := by
    unfold xEvaluatedFullSliceABABtensorAvg
    apply avgOver_congr
    rintro ⟨u, xy⟩
    dsimp [diag]
    calc
      (∑ h : Polynomial params, ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                (family.meas xy.2).toSubMeas.outcome h *
                (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a) *
            rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)))
        = ∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
                ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                  (family.meas xy.2).toSubMeas.outcome h *
                  (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a) *
              rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)) := by
            rw [Finset.sum_comm]
      _ = ∑ ah : Fq params × Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
                ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome ah.1 *
                  (family.meas xy.2).toSubMeas.outcome ah.2 *
                  (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome ah.1) *
              rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome ah.2)) := by
            exact (Fintype.sum_prod_type' (f := fun a : Fq params => fun h : Polynomial params =>
              ev strategy.state
                (leftTensor (ι₂ := ι)
                    ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                      (family.meas xy.2).toSubMeas.outcome h *
                      (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a) *
                  rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)))).symm
  rw [hdata]
  calc
    avgOver (uniformDistribution ((Point params × FullSliceQuestion params) × Point params))
        (fun r =>
          let A : SubMeas (Fq params) ι :=
            evaluateAt params r.1.1 ((family.meas r.1.2.1).toSubMeas)
          let B : SubMeas (Fq params) ι :=
            evaluateAt params r.2 ((family.meas r.1.2.2).toSubMeas)
          ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b * A.outcome a) *
                rightTensor (ι₁ := ι) (B.outcome b)))
      = avgOver 𝒟
          (fun ux =>
            avgOver (uniformDistribution (Point params))
              (fun v =>
                let A : SubMeas (Fq params) ι :=
                  evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
                let B : SubMeas (Fq params) ι :=
                  evaluateAt params v ((family.meas ux.2.2).toSubMeas)
                ∑ b : Fq params, ∑ a : Fq params,
                  ev strategy.state
                    (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b * A.outcome a) *
                      rightTensor (ι₁ := ι) (B.outcome b)))) := by
          exact avgOver_uniform_prod (f := fun ux : Point params × FullSliceQuestion params =>
            fun v : Point params =>
              let A : SubMeas (Fq params) ι :=
                evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
              let B : SubMeas (Fq params) ι :=
                evaluateAt params v ((family.meas ux.2.2).toSubMeas)
              ∑ b : Fq params, ∑ a : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b * A.outcome a) *
                    rightTensor (ι₁ := ι) (B.outcome b)))
    _ = avgOver 𝒟
          (fun ux =>
            diag ux + fullSliceABAByCollisionFactored params strategy family ux.1 ux.2) := by
          exact avgOver_congr 𝒟 _ _ hpoint
    _ = avgOver 𝒟 diag +
          avgOver 𝒟
            (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2) := by
          rw [avgOver_add]
    _ = xEvaluatedFullSliceABABtensorAvg params strategy family +
        avgOver (uniformDistribution (Point params × FullSliceQuestion params))
          (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2) := by
          rw [hdiag]



end MIPStarRE.LDT.Commutativity

end

end LIDT

open LIDT
/-!
# Full-slice y-marginalization endpoint

This module contains the y-side evaluated tensor marginalization block for the
`ABAB` full-slice tensor average.  It imports the collision and postprocessing
machinery from `Machinery.Marginalization.Core` and preserves the original
public marginalization theorem.

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
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι) (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized) :
    |_root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABtensorAvg params strategy family -
        _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABtensorAvg params strategy family| ≤
      (params.m * params.d : _root_.LIDT.MIPStarRE.LDT.Error) / params.q := by
  let R : _root_.LIDT.MIPStarRE.LDT.Error :=
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params))
      (fun ux => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAByCollisionFactored params strategy family ux.1 ux.2)
  have hR_nonneg : 0 ≤ R := by
    exact _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg _ _ (by
      intro ux
      exact _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAByCollisionFactored_nonneg params strategy family ux.1 ux.2)
  have hident := evaluatedSliceABABtensor_yEvaluation_eq_xFull_add_collision params strategy family
  have habs :
      |_root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABtensorAvg params strategy family -
        _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABtensorAvg params strategy family| = R := by
    rw [hident]
    change |_root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABtensorAvg params strategy family -
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABtensorAvg params strategy family + R)| = R
    have hdiff : _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABtensorAvg params strategy family -
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABtensorAvg params strategy family + R) = -R := by ring
    rw [hdiff, abs_neg, abs_of_nonneg hR_nonneg]
  rw [habs]
  exact _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAB_tensor_marginalize_y_collision_bound params strategy family hnorm
