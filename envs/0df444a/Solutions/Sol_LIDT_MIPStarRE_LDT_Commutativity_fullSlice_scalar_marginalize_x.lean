-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.fullSlice_scalar_marginalize_x
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:35:14.019216+00:00
-- url     : https://prove2.me/submissions/5d1aa1f6-3ec3-408c-926f-7749097f6aff

-- Generated proof for MIPStarRE.LDT.Commutativity.fullSlice_scalar_marginalize_x.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_switchSandwich_leftTransfer
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_switchSandwich_rightTransfer
import Theorems.Thm_LIDT_MIPStarRE_LDT_averageOperatorOverDistribution_mul_left_right

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/CommutativityPoints/Approximation.lean. -/
/-!
# Section 10 — commutativity points approximation layer

Restricted-diagonal approximation infrastructure for commutativity at points.
-/

@[expose] public section

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators







/-- Marginalizing a uniform point in `Point params.next` to its height
coordinate gives the uniform distribution on `Fq params`. -/
lemma avgOver_uniform_pointNext_height
    (params : Parameters) [FieldModel params.q]
    (f : Fq params → Error) :
    avgOver (uniformDistribution (Point params.next)) (fun u => f (pointHeight params u)) =
      avgOver (uniformDistribution (Fq params)) f := by
  simpa [pointNextEquiv] using
    (MIPStarRE.LDT.avgOver_uniform_equiv_snd
      (e := pointNextEquiv params) (f := f))





























end MIPStarRE.LDT.CommutativityPoints

end

/- Source helpers from MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/Completeness.lean. -/
/-!
# Switch-sandwich main: completeness estimate

`prop:switch-sandwich` assembled from the left and right transfer steps on a
normalized quantum state with a subprobability distribution.

## References

- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- `prop:switch-sandwich`.

The paper proof assumes a normalized state and a probability distribution
(weights summing to ≤ 1). These are now explicit hypotheses `hψ` and `h𝒟`. -/
theorem switchSandwich {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) (hB : OpBounded01 B)
    (δ : Error) :
    BipartiteSDDRel ψ 𝒟
      (IdxProjSubMeas.toIdxSubMeas A)
      (IdxProjSubMeas.toIdxSubMeas A) δ →
    SwitchSandwichStmt ψ 𝒟 A B δ := by
  intro happrox
  exact {
    leftSandwichTransfer :=
      switchSandwich_leftTransfer ψ 𝒟 hψ h𝒟 A B hB δ happrox
    rightSandwichTransfer :=
      switchSandwich_rightTransfer ψ 𝒟 hψ h𝒟 A B hB δ happrox
  }





end MIPStarRE.LDT.Preliminaries

end

/- Source helpers from MIPStarRE/LDT/Commutativity/Main/Auxiliary/ScalarMarginalization.lean. -/
/-!
# Section 11 commutativity: scalar marginalization lemmas

Schwartz–Zippel marginalization helpers (`eq:evaluate-gcom-at-points`,
`eq:gcom4-diff`) used in the final full-slice commutation theorem.

The public lemmas `fullSlice_scalar_marginalize_x` and
`fullSlice_scalar_marginalize_y` are pure scalar inequalities.  Their proofs
compose internal tensor-form comparisons over the tensor averages defined in
`Transport/FullSlice/Averages.lean`, with `closenessOfIP` at cost `√ζ` each.

See `docs/decisions/713-scalar-tensor-decision.md` for the full decision record.

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



/-- Triangle inequality with explicit bounds for an intermediate point. -/
private lemma abs_sub_le_of_two_step
    {a b c e₁ e₂ : Error}
    (hab : |a - b| ≤ e₁) (hbc : |b - c| ≤ e₂) :
    |a - c| ≤ e₁ + e₂ :=
  (abs_sub_le a b c).trans (add_le_add hab hbc)

/-- Summing the inner outcome in an `ABA` expectation turns it into the
submeasurement total. -/
private lemma sum_ev_leftTensor_sandwich_total
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι)) (A : MIPStarRE.Quantum.Op ι) (B : SubMeas α ι) :
    (∑ b : α, ev ψ (leftTensor (ι₂ := ι) (A * B.outcome b * A))) =
      ev ψ (leftTensor (ι₂ := ι) (A * B.total * A)) := by
  rw [← ev_sum ψ (fun b : α => leftTensor (ι₂ := ι) (A * B.outcome b * A))]
  congr 1
  rw [← B.sum_eq_total]
  rw [Matrix.mul_sum]
  rw [Matrix.sum_mul]
  rw [leftTensor_finset_sum]

/-- Summing the right-register outcome in the middle switch-sandwich term turns
it into the submeasurement total. -/
private lemma sum_ev_middle_total
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι)) (G : MIPStarRE.Quantum.Op ι) (A : SubMeas α ι) :
    (∑ a : α, ev ψ (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) (A.outcome a))) =
      ev ψ (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) A.total) := by
  rw [← ev_sum ψ (fun a : α => leftTensor (ι₂ := ι) G *
    rightTensor (ι₁ := ι) (A.outcome a))]
  congr 1
  rw [← A.sum_eq_total]
  rw [← Matrix.mul_sum]
  rw [rightTensor_finset_sum]

/-- Averaging the middle total in an `ABA` sandwich produces the averaged
slice operator `G = E_y Gʸ`. -/
private lemma avgOver_slice_total_left_sandwich_eq
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι)) (family : IdxPolyFamily params ι)
    (A : MIPStarRE.Quantum.Op ι) :
    avgOver (uniformDistribution (Fq params))
        (fun y => ev ψ (leftTensor (ι₂ := ι) (A * (family.meas y).total * A))) =
      ev ψ (leftTensor (ι₂ := ι) A *
        leftTensor (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total *
        leftTensor (ι₂ := ι) A) := by
  rw [← ev_leftTensor_averageOperatorOverDistribution ψ (uniformDistribution (Fq params))
    (fun y => A * (family.meas y).total * A)]
  rw [averageOperatorOverDistribution_mul_left_right]
  simp [IdxPolyFamily.averagedSubMeas, averageIdxSubMeas,
    leftTensor_mul_leftTensor, mul_assoc]

/-- Full-slice cubic first term as the left switch-sandwich expectation. -/
private lemma fullSliceABAAvg_eq_leftSandwichExpectation
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    fullSliceABAAvg params strategy family =
      MIPStarRE.LDT.Preliminaries.leftSandwichExpectation strategy.state
        (uniformDistribution (Fq params)) family.meas
        ((IdxPolyFamily.averagedSubMeas family).total) := by
  classical
  unfold fullSliceABAAvg MIPStarRE.LDT.Preliminaries.leftSandwichExpectation
  rw [avgOver_uniform_prod (α := Fq params) (β := Fq params) (f := fun x y =>
    ∑ gh : FullSliceOutcome params,
      ev strategy.state (leftTensor (ι₂ := ι)
        ((family.meas x).toSubMeas.outcome gh.1 *
          (family.meas y).toSubMeas.outcome gh.2 *
          (family.meas x).toSubMeas.outcome gh.1)))]
  apply avgOver_congr
  intro x
  simp only [Fintype.sum_prod_type]
  rw [avgOver_sum]
  apply Finset.sum_congr rfl
  intro g _
  calc
    avgOver (uniformDistribution (Fq params))
        (fun y => ∑ h : Polynomial params,
          ev strategy.state (leftTensor (ι₂ := ι)
            ((family.meas x).outcome g * (family.meas y).outcome h *
              (family.meas x).outcome g)))
        = avgOver (uniformDistribution (Fq params))
            (fun y => ev strategy.state (leftTensor (ι₂ := ι)
              ((family.meas x).outcome g * (family.meas y).total *
                (family.meas x).outcome g))) := by
            apply avgOver_congr
            intro y
            exact sum_ev_leftTensor_sandwich_total strategy.state
              ((family.meas x).outcome g) (family.meas y).toSubMeas
    _ = ev strategy.state
          (leftTensor (ι₂ := ι) ((family.meas x).outcome g) *
            leftTensor (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total *
            leftTensor (ι₂ := ι) ((family.meas x).outcome g)) := by
            exact avgOver_slice_total_left_sandwich_eq params strategy.state family
              ((family.meas x).outcome g)

/-- Evaluated-slice cubic first term as the evaluated left switch-sandwich expectation. -/
private lemma evaluatedSliceABAAvg_eq_leftSandwichExpectation
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    evaluatedSliceABAAvg params strategy family =
      MIPStarRE.LDT.Preliminaries.leftSandwichExpectation strategy.state
        (uniformDistribution (Point params.next))
        (evaluatedPointProj params family)
        ((IdxPolyFamily.averagedSubMeas family).total) := by
  classical
  unfold evaluatedSliceABAAvg MIPStarRE.LDT.Preliminaries.leftSandwichExpectation
    evaluatedPointProj
  change avgOver (uniformDistribution (Point params.next × Point params.next))
      (fun uv => (fun u v => ∑ ab : Fq params × Fq params,
        evaluatedSliceABATerm params strategy family (u, v) ab) uv.1 uv.2) =
    avgOver (uniformDistribution (Point params.next))
      (fun q => ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι) ((evaluatedPointFamily params family q).outcome a) *
            leftTensor (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total *
            leftTensor (ι₂ := ι) ((evaluatedPointFamily params family q).outcome a)))
  rw [avgOver_uniform_prod (α := Point params.next) (β := Point params.next)
    (f := fun u v => ∑ ab : Fq params × Fq params,
      evaluatedSliceABATerm params strategy family (u, v) ab)]
  apply avgOver_congr
  intro u
  simp only [Fintype.sum_prod_type]
  rw [avgOver_sum]
  apply Finset.sum_congr rfl
  intro a _
  unfold evaluatedSliceABATerm
  calc
    avgOver (uniformDistribution (Point params.next))
        (fun v => ∑ b : Fq params,
          ev strategy.state (leftTensor (ι₂ := ι)
            ((evaluatedPointFamily params family u).outcome a *
              (evaluatedPointFamily params family v).outcome b *
              (evaluatedPointFamily params family u).outcome a)))
        = avgOver (uniformDistribution (Point params.next))
            (fun v => ev strategy.state (leftTensor (ι₂ := ι)
              ((evaluatedPointFamily params family u).outcome a *
                (evaluatedPointFamily params family v).total *
                (evaluatedPointFamily params family u).outcome a))) := by
            apply avgOver_congr
            intro v
            exact sum_ev_leftTensor_sandwich_total strategy.state
              ((evaluatedPointFamily params family u).outcome a)
              (evaluatedPointFamily params family v)
    _ = avgOver (uniformDistribution (Fq params))
          (fun y => ev strategy.state (leftTensor (ι₂ := ι)
            ((evaluatedPointFamily params family u).outcome a *
              (family.meas y).total *
              (evaluatedPointFamily params family u).outcome a))) := by
            have h := CommutativityPoints.avgOver_uniform_pointNext_height params
              (fun y : Fq params => ev strategy.state (leftTensor (ι₂ := ι)
                ((evaluatedPointFamily params family u).outcome a *
                  (family.meas y).total *
                  (evaluatedPointFamily params family u).outcome a)))
            rw [← h]
            apply avgOver_congr
            intro v
            simp [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
              postprocess_total]
    _ = ev strategy.state
          (leftTensor (ι₂ := ι) ((evaluatedPointFamily params family u).outcome a) *
            leftTensor (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total *
            leftTensor (ι₂ := ι) ((evaluatedPointFamily params family u).outcome a)) := by
            exact avgOver_slice_total_left_sandwich_eq params strategy.state family
              ((evaluatedPointFamily params family u).outcome a)

/-- The full and evaluated switch-sandwich middle terms are the same `G ⊗ G` average. -/
private lemma fullSlice_middleSandwichExpectation_eq_evaluated
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    MIPStarRE.LDT.Preliminaries.middleSandwichExpectation strategy.state
        (uniformDistribution (Fq params)) family.meas
        ((IdxPolyFamily.averagedSubMeas family).total) =
      MIPStarRE.LDT.Preliminaries.middleSandwichExpectation strategy.state
        (uniformDistribution (Point params.next))
        (evaluatedPointProj params family)
        ((IdxPolyFamily.averagedSubMeas family).total) := by
  classical
  unfold MIPStarRE.LDT.Preliminaries.middleSandwichExpectation evaluatedPointProj
  let G : MIPStarRE.Quantum.Op ι := (IdxPolyFamily.averagedSubMeas family).total
  change avgOver (uniformDistribution (Fq params))
      (fun x => ∑ a : Polynomial params,
        ev strategy.state (leftTensor (ι₂ := ι) G *
          rightTensor (ι₁ := ι) ((family.meas x).outcome a))) =
    avgOver (uniformDistribution (Point params.next))
      (fun u => ∑ a : Fq params,
        ev strategy.state (leftTensor (ι₂ := ι) G *
          rightTensor (ι₁ := ι) ((evaluatedPointFamily params family u).outcome a)))
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => ∑ a : Polynomial params,
          ev strategy.state (leftTensor (ι₂ := ι) G *
            rightTensor (ι₁ := ι) ((family.meas x).outcome a))) =
      avgOver (uniformDistribution (Fq params))
        (fun x => ev strategy.state (leftTensor (ι₂ := ι) G *
          rightTensor (ι₁ := ι) ((family.meas x).total))) := by
        apply avgOver_congr
        intro x
        exact sum_ev_middle_total strategy.state G (family.meas x).toSubMeas
    _ = avgOver (uniformDistribution (Point params.next))
        (fun u => ev strategy.state (leftTensor (ι₂ := ι) G *
          rightTensor (ι₁ := ι) ((evaluatedPointFamily params family u).total))) := by
        symm
        calc
          avgOver (uniformDistribution (Point params.next))
              (fun u => ev strategy.state (leftTensor (ι₂ := ι) G *
                rightTensor (ι₁ := ι) ((evaluatedPointFamily params family u).total))) =
            avgOver (uniformDistribution (Point params.next))
              (fun u => ev strategy.state (leftTensor (ι₂ := ι) G *
                rightTensor (ι₁ := ι) ((family.meas (pointHeight params u)).total))) := by
              apply avgOver_congr
              intro u
              simp [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
                postprocess_total]
          _ = avgOver (uniformDistribution (Fq params))
              (fun x => ev strategy.state (leftTensor (ι₂ := ι) G *
                rightTensor (ι₁ := ι) ((family.meas x).total))) := by
              exact CommutativityPoints.avgOver_uniform_pointNext_height params
                (fun x : Fq params => ev strategy.state (leftTensor (ι₂ := ι) G *
                  rightTensor (ι₁ := ι) ((family.meas x).total)))
    _ = avgOver (uniformDistribution (Point params.next))
        (fun u => ∑ a : Fq params,
          ev strategy.state (leftTensor (ι₂ := ι) G *
            rightTensor (ι₁ := ι) ((evaluatedPointFamily params family u).outcome a))) := by
        apply avgOver_congr
        intro u
        exact (sum_ev_middle_total strategy.state G (evaluatedPointFamily params family u)).symm





end MIPStarRE.LDT.Commutativity

end

end LIDT

open LIDT
/-!
# Section 11 commutativity: scalar marginalization lemmas

Schwartz–Zippel marginalization helpers (`eq:evaluate-gcom-at-points`,
`eq:gcom4-diff`) used in the final full-slice commutation theorem.

The public lemmas `fullSlice_scalar_marginalize_x` and
`fullSlice_scalar_marginalize_y` are pure scalar inequalities.  Their proofs
compose internal tensor-form comparisons over the tensor averages defined in
`Transport/FullSlice/Averages.lean`, with `closenessOfIP` at cost `√ζ` each.

See `docs/decisions/713-scalar-tensor-decision.md` for the full decision record.

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
    (zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAAvg params strategy family -
        _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family| ≤
      4 * Real.sqrt zeta := by
  let G : _root_.LIDT.MIPStarRE.Quantum.Op ι := (_root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.averagedSubMeas family).total
  have hG : _root_.LIDT.MIPStarRE.LDT.Preliminaries.OpBounded01 G := by
    refine ⟨?_, ?_⟩
    · simpa [G] using (_root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.averagedSubMeas family).total_nonneg
    · simpa [G] using sub_nonneg.mpr (_root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.averagedSubMeas family).total_le_one
  have hfullApprox :
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.BipartiteSDDRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
        (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas family.meas)
        (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas family.meas) zeta := by
    refine ⟨?_⟩
    simpa [_root_.LIDT.MIPStarRE.LDT.Preliminaries.BipartiteSDDRel]
      using hself.sliceSelfConsistency.squaredDistanceBound
  have hfullSwitch :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.switchSandwich strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) hnorm
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Fq params))
      family.meas G hG zeta hfullApprox
  have hevalRel :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
      params strategy family zeta hself
  have hevalApprox :
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.BipartiteSDDRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas (evaluatedPointProj params family))
        (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas (evaluatedPointProj params family)) zeta := by
    refine ⟨?_⟩
    have hleft :
        _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft params family =
          _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft
            (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas (evaluatedPointProj params family)) := by
      funext u
      rfl
    have hright :
        _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyRight params family =
          _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight
            (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas (evaluatedPointProj params family)) := by
      funext u
      rfl
    rw [← hleft, ← hright]
    exact hevalRel.squaredDistanceBound
  have hevalSwitch :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.switchSandwich strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next)) hnorm
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      (evaluatedPointProj params family) G hG zeta hevalApprox
  let fullCenter : _root_.LIDT.MIPStarRE.LDT.Error :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) family.meas G
  let evalCenter : _root_.LIDT.MIPStarRE.LDT.Error :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next)) (evaluatedPointProj params family) G
  have hfull :
      |_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAAvg params strategy family - fullCenter| ≤ 2 * Real.sqrt zeta := by
    simpa [fullCenter, G, fullSliceABAAvg_eq_leftSandwichExpectation]
      using hfullSwitch.leftSandwichTransfer
  have heval :
      |evalCenter - _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family| ≤ 2 * Real.sqrt zeta := by
    have h := hevalSwitch.leftSandwichTransfer
    have h' : |_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family - evalCenter| ≤
        2 * Real.sqrt zeta := by
      simpa [evalCenter, G, evaluatedSliceABAAvg_eq_leftSandwichExpectation] using h
    rwa [abs_sub_comm]
  have hcenter : fullCenter = evalCenter := by
    simpa [fullCenter, evalCenter, G]
      using fullSlice_middleSandwichExpectation_eq_evaluated params strategy family
  have htri := abs_sub_le_of_two_step hfull (by simpa [hcenter] using heval)
  calc
    |_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAAvg params strategy family - _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family|
      ≤ 2 * Real.sqrt zeta + 2 * Real.sqrt zeta := htri
    _ = 4 * Real.sqrt zeta := by ring
