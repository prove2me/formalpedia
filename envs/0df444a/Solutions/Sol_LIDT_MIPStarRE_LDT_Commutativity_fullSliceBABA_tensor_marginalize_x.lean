-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABA_tensor_marginalize_x
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:05:52.267815+00:00
-- url     : https://prove2.me/submissions/4e8f6eb5-a582-4e6e-8e61-99d09b778072

-- Generated proof for MIPStarRE.LDT.Commutativity.fullSliceBABA_tensor_marginalize_x.
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



/-- The Schwartz-Zippel/PSD bound for the x-marginalization collision residual.

This is the proved hard estimate used by the staged x-marginalization tensor
lemma below.  The algebraic expansion identifies the x-evaluated tensor-average
difference with this residual averaged over `x,y`. -/
private lemma fullSliceBABAxCollisionFactored_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized)
    (xy : FullSliceQuestion params) :
    fullSliceBABAxCollisionFactored params strategy family xy ≤
      (params.m * params.d : Error) / params.q := by
  let A : SubMeas (Polynomial params) ι := (family.meas xy.1).toSubMeas
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  simpa [fullSliceBABAxCollisionFactored, A, B] using
    MIPStarRE.LDT.Preliminaries.polynomialCollision_sandwichTensor_le_mdq
      params strategy.state hnorm B A A





/-- Averaged x-collision bound in the form consumed by
`fullSliceBABA_tensor_marginalize_x`. -/
lemma fullSliceBABA_tensor_marginalize_x_collision_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized) :
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun xy => fullSliceBABAxCollisionFactored params strategy family xy) ≤
      (params.m * params.d : Error) / params.q := by
  let δ : Error := (params.m * params.d : Error) / params.q
  exact avgOver_uniform_le_const
    (α := FullSliceQuestion params)
    (fun xy => fullSliceBABAxCollisionFactored params strategy family xy)
    δ
    (by
      intro xy
      simpa [δ] using
        fullSliceBABAxCollisionFactored_le_mdq params strategy family hnorm xy)













/-- The x-collision residual is nonnegative term-by-term. -/
private lemma fullSliceBABAxCollisionFactored_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (xy : FullSliceQuestion params) :
    0 ≤ fullSliceBABAxCollisionFactored params strategy family xy := by
  classical
  let A : SubMeas (Polynomial params) ι := (family.meas xy.1).toSubMeas
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  have hcoef_nonneg (gg : Polynomial params × Polynomial params) :
      0 ≤ (if gg.1 = gg.2 then 0 else
        avgOver (uniformDistribution (Point params))
          (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) := by
    by_cases hEq : gg.1 = gg.2
    · simp [hEq]
    · have hnonneg :
          0 ≤ avgOver (uniformDistribution (Point params))
            (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0) := by
        exact avgOver_nonneg _ _ (by
          intro u
          by_cases hu : gg.1 u = gg.2 u <;> simp [hu])
      simpa [hEq] using hnonneg
  have hsum :
      0 ≤ ∑ gg : Polynomial params × Polynomial params, ∑ h : Polynomial params,
        (if gg.1 = gg.2 then 0 else
          avgOver (uniformDistribution (Point params))
            (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) *
          ev strategy.state
            (leftTensor (ι₂ := ι) (B.outcome h * A.outcome gg.1 * B.outcome h) *
              rightTensor (ι₁ := ι) (A.outcome gg.2)) := by
    refine Finset.sum_nonneg ?_
    intro gg _
    refine Finset.sum_nonneg ?_
    intro h _
    exact mul_nonneg (hcoef_nonneg gg)
      (sandwichTensorSummand_nonneg strategy.state B A A h gg.1 gg.2)
  simpa [fullSliceBABAxCollisionFactored, A, B] using hsum



/-- Exact x-side postprocessing identity: the x-evaluated `BAB ⊗ A` tensor
average is the full tensor average plus the x-collision residual. -/
private lemma fullSliceBABAtensor_xEvaluation_eq_full_add_collision
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    xEvaluatedSliceBABAtensorAvg params strategy family =
      fullSliceBABAtensorAvg params strategy family +
        avgOver (uniformDistribution (FullSliceQuestion params))
          (fun xy => fullSliceBABAxCollisionFactored params strategy family xy) := by
  classical
  let 𝒟 : Distribution (FullSliceQuestion params) :=
    uniformDistribution (FullSliceQuestion params)
  let diag : FullSliceQuestion params → Error := fun xy =>
    ∑ g : Polynomial params, ∑ h : Polynomial params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            ((family.meas xy.2).toSubMeas.outcome h *
              (family.meas xy.1).toSubMeas.outcome g *
              (family.meas xy.2).toSubMeas.outcome h) *
          rightTensor (ι₁ := ι) ((family.meas xy.1).toSubMeas.outcome g))
  have hpoint (xy : FullSliceQuestion params) :
      avgOver (uniformDistribution (Point params))
        (fun u =>
          let A : SubMeas (Fq params) ι :=
            evaluateAt params u ((family.meas xy.1).toSubMeas)
          let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
          ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (B.outcome h * A.outcome a * B.outcome h) *
                rightTensor (ι₁ := ι) (A.outcome a))) =
        diag xy + fullSliceBABAxCollisionFactored params strategy family xy := by
    let A : SubMeas (Polynomial params) ι := (family.meas xy.1).toSubMeas
    let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
    simpa [diag, fullSliceBABAxCollisionFactored, A, B, evaluateAt] using
      (avg_postprocess_sandwichTensor_eq_diag_add_collision
        (ψ := strategy.state) (A := A) (B := B)
        (eval := fun u : Point params => fun g : Polynomial params => g u))
  have hdiag : avgOver 𝒟 diag = fullSliceBABAtensorAvg params strategy family := by
    unfold fullSliceBABAtensorAvg
    apply avgOver_congr
    intro xy
    dsimp [diag]
    simpa using
      (Fintype.sum_prod_type' (f := fun g : Polynomial params => fun h : Polynomial params =>
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((family.meas xy.2).toSubMeas.outcome h *
                (family.meas xy.1).toSubMeas.outcome g *
                (family.meas xy.2).toSubMeas.outcome h) *
            rightTensor (ι₁ := ι)
              ((family.meas xy.1).toSubMeas.outcome g)))).symm
  unfold xEvaluatedSliceBABAtensorAvg
  calc
    avgOver 𝒟
        (fun xy =>
          avgOver (uniformDistribution (Point params))
            (fun u =>
              let A : SubMeas (Fq params) ι :=
                evaluateAt params u ((family.meas xy.1).toSubMeas)
              let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
              ∑ a : Fq params, ∑ h : Polynomial params,
                ev strategy.state
                  (leftTensor (ι₂ := ι) (B.outcome h * A.outcome a * B.outcome h) *
                    rightTensor (ι₁ := ι) (A.outcome a))))
      = avgOver 𝒟
          (fun xy => diag xy + fullSliceBABAxCollisionFactored params strategy family xy) := by
          exact avgOver_congr 𝒟 _ _ hpoint
    _ = avgOver 𝒟 diag +
          avgOver 𝒟 (fun xy => fullSliceBABAxCollisionFactored params strategy family xy) := by
          rw [avgOver_add]
    _ = fullSliceBABAtensorAvg params strategy family +
          avgOver (uniformDistribution (FullSliceQuestion params))
            (fun xy => fullSliceBABAxCollisionFactored params strategy family xy) := by
          rw [hdiag]



end MIPStarRE.LDT.Commutativity

end

end LIDT

open LIDT
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
    |_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABAtensorAvg params strategy family -
        _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedSliceBABAtensorAvg params strategy family| ≤
      (params.m * params.d : _root_.LIDT.MIPStarRE.LDT.Error) / params.q := by
  let R : _root_.LIDT.MIPStarRE.LDT.Error :=
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params))
      (fun xy => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABAxCollisionFactored params strategy family xy)
  have hR_nonneg : 0 ≤ R := by
    exact _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg _ _ (by
      intro xy
      exact fullSliceBABAxCollisionFactored_nonneg params strategy family xy)
  have hident := fullSliceBABAtensor_xEvaluation_eq_full_add_collision params strategy family
  have habs :
      |_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABAtensorAvg params strategy family -
        _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedSliceBABAtensorAvg params strategy family| = R := by
    rw [hident]
    change |_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABAtensorAvg params strategy family -
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABAtensorAvg params strategy family + R)| = R
    have hdiff : _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABAtensorAvg params strategy family -
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABAtensorAvg params strategy family + R) = -R := by ring
    rw [hdiff, abs_neg, abs_of_nonneg hR_nonneg]
  rw [habs]
  exact _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABA_tensor_marginalize_x_collision_bound params strategy family hnorm
