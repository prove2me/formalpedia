-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.gCommStabilityTwo_raw_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:50:30.112769+00:00
-- url     : https://prove2.me/submissions/9b4c181d-cd4f-473a-8142-600fda14bba6

-- Generated proof for MIPStarRE.LDT.Commutativity.gCommStabilityTwo_raw_scalar.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
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
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Basic/TensorPlacement.lean. -/
/-!
# Tensor-placement helper lemmas and sandwich tensor estimates

Tensor-sum commutation, positivity/boundedness preservation,
factoring lemmas, and sandwich-residual estimates used in
the main induction step and polynomial-agreement arguments.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Tensor-placement helper lemmas -/

























/-- A complex scalar on the right register factors out of a bipartite tensor product.

This is the tensor-placement version of bilinearity of `opTensor`: placing
`c • B` on the right and multiplying by the left placement of `A` equals the
same scalar multiplying `leftTensor A * rightTensor B`. -/
theorem leftTensor_mul_rightTensor_smul_right
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : Error) (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) ((c : ℂ) • B) =
      (c : ℂ) • (leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) B) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
  simpa [opTensor] using Matrix.kronecker_smul (c : ℂ) A B



/-- A real scalar on the right register factors out of a bipartite tensor product.

This restates `leftTensor_mul_rightTensor_smul_right` for the real scalar action
used by `averageOperatorOverDistribution`, coercing the real scalar to `ℂ` on
the tensor product. -/
theorem leftTensor_mul_rightTensor_real_smul_right
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : Error) (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) (c • B) =
      (c : ℂ) • (leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) B) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact leftTensor_mul_rightTensor_smul_right c A B











namespace SubMeas



end SubMeas

/-! ### Sandwich tensor estimates -/





end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/Commutativity/GCommStability/Scalar/Common.lean. -/
/-!
# Section 11 commutativity: shared scalar stability helpers

Auxiliary positivity, order, and bounded-residual lemmas used by the scalar stability estimates.
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace GCommStability.Scalar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma averagedSlicePointEvaluationOperator_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) :
    0 ≤ IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g := by
  unfold IdxPolyFamily.averagedSlicePointEvaluationOperator
  exact averageOperatorOverDistribution_nonneg (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u))
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).outcome_pos (g u))

lemma averagedSlicePointEvaluationOperator_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) :
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤ 1 := by
  unfold IdxPolyFamily.averagedSlicePointEvaluationOperator
  exact averageOperatorOverDistribution_uniform_le_one
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u))
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).outcome_le_one (g u))

lemma averagedSlicePointEvaluationOperator_hermitian
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) :
    (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g)ᴴ =
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g := by
  exact
    (Matrix.nonneg_iff_posSemidef.mp
      (averagedSlicePointEvaluationOperator_nonneg params strategy x g)).isHermitian.eq

lemma averagedSlicePointEvaluationOperator_sq_le_self
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) :
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g *
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g := by
  exact MIPStarRE.Quantum.sq_le_self
    (averagedSlicePointEvaluationOperator_nonneg params strategy x g)
    (averagedSlicePointEvaluationOperator_le_one params strategy x g)

lemma storedResidual_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (zeta : Error)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ∀ x : Fq params, 0 ≤ hbound.storedResidual G x := by
  intro x
  unfold IdxPolyFamily.SliceBoundednessInput.storedResidual
  apply ev_nonneg_of_psd
  rw [leftTensor_mul_rightTensor_eq_opTensor]
  simpa [opTensor] using
    MIPStarRE.Quantum.kronecker_nonneg
      (sub_nonneg.mpr (G x).total_le_one)
      (hbound.sliceOpPSD x)


end GCommStability.Scalar

end MIPStarRE.LDT.Commutativity

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









































namespace SliceBoundednessInput



/-- Stored residual half of the boundedness hypothesis.

This is exactly the paper's `(I-G^x) ⊗ Z^x` residual bound from
`references/ldt-paper/commutativity-G.tex`. -/
theorem storedBoundedResidualBound {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SymStrat params.next ι}
    {family : IdxPolyFamily params ι} {zeta : Error}
    (hbound : SliceBoundednessInput strategy family zeta)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    avgOver (uniformDistribution (Fq params))
      (fun x => hbound.storedResidual G x) ≤ zeta := by
  simpa [storedResidual, hG] using hbound.sliceBoundedness

/-- Paper-faithful domination half of the boundedness hypothesis.

This is the line `Z^x ≥ E_u A^{u,x}_{g(u)}` from
`references/ldt-paper/commutativity-G.tex`. -/
theorem averagedPoint_le_witness {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SymStrat params.next ι}
    {family : IdxPolyFamily params ι} {zeta : Error}
    (hbound : SliceBoundednessInput strategy family zeta) :
    ∀ x : Fq params, ∀ g : Polynomial params,
      averagedSlicePointEvaluationOperator strategy x g ≤ family.witness x :=
  hbound.sliceDominatesAveragedPoint

end SliceBoundednessInput

end IdxPolyFamily

end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/Commutativity/GCommStability/Scalar/RawSecond.lean. -/
/-!
# Section 11 commutativity: raw second scalar stability bound

The raw uncollapsed form of the second scalar stability estimate.
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open GCommStability.Scalar
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma avgOver_right_linear
    {U Γ Aidx : Type*} [Fintype Γ] [Fintype Aidx]
    (𝒟U : Distribution U)
    (ψ : QuantumState (ι × ι))
    (L : Γ → Aidx → MIPStarRE.Quantum.Op ι)
    (P : Aidx → MIPStarRE.Quantum.Op ι)
    (Q : U → Γ → MIPStarRE.Quantum.Op ι) :
    avgOver 𝒟U (fun u =>
      ∑ g : Γ, ∑ a : Aidx,
        ev ψ (leftTensor (ι₂ := ι) (L g a) *
          rightTensor (ι₁ := ι) (P a * Q u g))) =
    ∑ g : Γ, ∑ a : Aidx,
        ev ψ (leftTensor (ι₂ := ι) (L g a) *
          rightTensor (ι₁ := ι)
            (P a * averageOperatorOverDistribution 𝒟U (fun u => Q u g))) := by
  classical
  let T : U → Γ → Aidx → Error := fun u g a =>
    ev ψ (leftTensor (ι₂ := ι) (L g a) * rightTensor (ι₁ := ι) (P a * Q u g)) *
      𝒟U.weight u
  calc
    avgOver 𝒟U (fun u =>
      ∑ g : Γ, ∑ a : Aidx,
        ev ψ (leftTensor (ι₂ := ι) (L g a) *
          rightTensor (ι₁ := ι) (P a * Q u g)))
      = ∑ u ∈ 𝒟U.support, ∑ g : Γ, ∑ a : Aidx, T u g a := by
        simp [avgOver, T, Finset.mul_sum, mul_comm]
    _ = ∑ g : Γ, ∑ a : Aidx, ∑ u ∈ 𝒟U.support, T u g a := by
        calc
          ∑ u ∈ 𝒟U.support, ∑ g : Γ, ∑ a : Aidx, T u g a
            = ∑ g : Γ, ∑ u ∈ 𝒟U.support, ∑ a : Aidx, T u g a := by
              rw [Finset.sum_comm]
          _ = ∑ g : Γ, ∑ a : Aidx, ∑ u ∈ 𝒟U.support, T u g a := by
              refine Finset.sum_congr rfl ?_
              intro g _
              rw [Finset.sum_comm]
      _ = ∑ g : Γ, ∑ a : Aidx,
          ev ψ (leftTensor (ι₂ := ι) (L g a) *
            rightTensor (ι₁ := ι)
              (P a * averageOperatorOverDistribution 𝒟U (fun u => Q u g))) := by
          suffices
              ∑ g : Γ, ∑ a : Aidx, ∑ u ∈ 𝒟U.support,
                  ev ψ (leftTensor (ι₂ := ι) (L g a) *
                      rightTensor (ι₁ := ι) (P a * Q u g)) * 𝒟U.weight u =
                ∑ g : Γ, ∑ a : Aidx, ∑ u ∈ 𝒟U.support,
                  ev ψ ((𝒟U.weight u : Error) •
                    (leftTensor (ι₂ := ι) (L g a) *
                      rightTensor (ι₁ := ι) (P a * Q u g))) by
            simpa [T, averageOperatorOverDistribution, ev_finset_sum,
              ← rightTensor_finset_sum, leftTensor_mul_rightTensor_real_smul_right,
              Matrix.mul_sum] using this
          refine Finset.sum_congr rfl ?_
          intro g _
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro u _
          let X : MIPStarRE.Quantum.Op (ι × ι) :=
            leftTensor (ι₂ := ι) (L g a) * rightTensor (ι₁ := ι) (P a * Q u g)
          change ev ψ X * 𝒟U.weight u = ev ψ ((𝒟U.weight u : Error) • X)
          rw [ev_real_smul]
          ring

private lemma sum_ev_leftTensor_mul_rightTensor_const
    {α : Type*} (s : Finset α)
    (ψ : QuantumState (ι × ι))
    (L : α → MIPStarRE.Quantum.Op ι)
    (R : MIPStarRE.Quantum.Op ι) :
    ∑ a ∈ s, ev ψ (leftTensor (ι₂ := ι) (L a) * rightTensor (ι₁ := ι) R) =
      ev ψ (leftTensor (ι₂ := ι) (∑ a ∈ s, L a) * rightTensor (ι₁ := ι) R) := by
  classical
  calc
    ∑ a ∈ s, ev ψ (leftTensor (ι₂ := ι) (L a) * rightTensor (ι₁ := ι) R)
      = ev ψ ((∑ a ∈ s, leftTensor (ι₂ := ι) (L a)) * rightTensor (ι₁ := ι) R) := by
        simp [ev_finset_sum, Finset.sum_mul]
    _ = ev ψ (leftTensor (ι₂ := ι) (∑ a ∈ s, L a) * rightTensor (ι₁ := ι) R) := by
        rw [leftTensor_finset_sum]



private lemma gCommStabilityTwo_raw_left_sum_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (x : Fq params) (vy : Point params.next) :
    ∑ gb : Polynomial params × Fq params,
        ((1 - (G x).total) *
          ((evaluatedPointFamily params family vy).outcome gb.2 *
            (G x).outcome gb.1 *
            (evaluatedPointFamily params family vy).outcome gb.2) *
          (1 - (G x).total)) ≤
      1 - (G x).total := by
  classical
  let B : SubMeas (Fq params) ι := evaluatedPointFamily params family vy
  let T : MIPStarRE.Quantum.Op ι := (G x).total
  have hT_herm : Tᴴ = T := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [T] using (G x).total_nonneg).isHermitian.eq
  have hTc_herm : (1 - T)ᴴ = 1 - T := by simp [hT_herm]
  have hT_proj : T * T = T := by
    simpa [T, hG] using
      MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj (family.meas x)
  have hinner_le :
      ∑ gb : Polynomial params × Fq params,
          B.outcome gb.2 * (G x).outcome gb.1 * B.outcome gb.2 ≤
        (1 : MIPStarRE.Quantum.Op ι) := by
    calc
      ∑ gb : Polynomial params × Fq params,
          B.outcome gb.2 * (G x).outcome gb.1 * B.outcome gb.2
        = ∑ b : Fq params, ∑ g : Polynomial params,
            B.outcome b * (G x).outcome g * B.outcome b := by
          calc
            ∑ gb : Polynomial params × Fq params,
                B.outcome gb.2 * (G x).outcome gb.1 * B.outcome gb.2
              = ∑ g : Polynomial params, ∑ b : Fq params,
                  B.outcome b * (G x).outcome g * B.outcome b := by
                rw [Fintype.sum_prod_type]
            _ = ∑ b : Fq params, ∑ g : Polynomial params,
                  B.outcome b * (G x).outcome g * B.outcome b := by
                rw [Finset.sum_comm]
      _ = ∑ b : Fq params, B.outcome b * T * B.outcome b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          calc
            ∑ g : Polynomial params, B.outcome b * (G x).outcome g * B.outcome b
              = (∑ g : Polynomial params, B.outcome b * (G x).outcome g) * B.outcome b := by
                rw [Finset.sum_mul]
            _ = (B.outcome b * ∑ g : Polynomial params, (G x).outcome g) *
                  B.outcome b := by
                rw [Matrix.mul_sum]
            _ = B.outcome b * T * B.outcome b := by
                rw [(G x).sum_eq_total]
      _ ≤ ∑ b : Fq params, B.outcome b := by
          refine Finset.sum_le_sum ?_
          intro b _
          calc
            B.outcome b * T * B.outcome b ≤ B.outcome b * 1 * B.outcome b := by
              exact IsSelfAdjoint.conjugate_le_conjugate
                (G x).total_le_one (B.outcome_hermitian b)
            _ = B.outcome b := by
              simp [B, evaluatedPointFamily_outcome_proj params family vy b]
      _ = B.total := B.sum_eq_total
      _ ≤ 1 := B.total_le_one
  calc
    ∑ gb : Polynomial params × Fq params,
        ((1 - (G x).total) *
          ((evaluatedPointFamily params family vy).outcome gb.2 *
            (G x).outcome gb.1 *
            (evaluatedPointFamily params family vy).outcome gb.2) *
          (1 - (G x).total))
      = (1 - T) *
          (∑ gb : Polynomial params × Fq params,
            B.outcome gb.2 * (G x).outcome gb.1 * B.outcome gb.2) *
          (1 - T) := by
        simp [B, T, Matrix.mul_sum, Finset.sum_mul, mul_assoc]
    _ ≤ (1 - T) * 1 * (1 - T) := by
        exact IsSelfAdjoint.conjugate_le_conjugate hinner_le hTc_herm
    _ = 1 - T := by
        calc
          (1 - T) * 1 * (1 - T) = (1 - T) * (1 - T) := by simp
          _ = 1 - T - T + T * T := by noncomm_ring
          _ = 1 - T := by simp [hT_proj]

private lemma gCommStabilityTwo_raw_scalar_pointwise_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ∀ x : Fq params,
      |gCommStabilityTwoRawScalarDefect params strategy family G x| ≤
        Real.sqrt (hbound.storedResidual G x) := by
  classical
  intro x
  let 𝒟V : Distribution (Point params.next) := uniformDistribution (Point params.next)
  let 𝒟U : Distribution (Point params) := uniformDistribution (Point params)
  let T : MIPStarRE.Quantum.Op ι := (G x).total
  let W : Polynomial params → MIPStarRE.Quantum.Op ι :=
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x
  let X : Point params.next → Polynomial params × Fq params →
      MIPStarRE.Quantum.Op (ι × ι) := fun vy gb =>
    leftTensor (ι₂ := ι) ((G x).outcome gb.1) *
      rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2)
  let Y : Point params.next → Polynomial params × Fq params →
      MIPStarRE.Quantum.Op (ι × ι) := fun vy gb =>
    leftTensor (ι₂ := ι)
        ((G x).outcome gb.1 *
          (evaluatedPointFamily params family vy).outcome gb.2 * (1 - T)) *
      rightTensor (ι₁ := ι) (W gb.1)
  let xDiag : Point params.next → Polynomial params × Fq params → Error := fun vy gb =>
    ev strategy.state (X vy gb * (X vy gb)ᴴ)
  let yDiag : Point params.next → Polynomial params × Fq params → Error := fun vy gb =>
    ev strategy.state
      (leftTensor (ι₂ := ι)
          ((1 - T) *
            ((evaluatedPointFamily params family vy).outcome gb.2 *
              (G x).outcome gb.1 *
              (evaluatedPointFamily params family vy).outcome gb.2) *
            (1 - T)) *
        rightTensor (ι₁ := ι) (family.witness x))
  let t : Point params.next → Polynomial params × Fq params → Error := fun vy gb =>
    ev strategy.state
      (leftTensor (ι₂ := ι)
          ((G x).outcome gb.1 *
            (evaluatedPointFamily params family vy).outcome gb.2 * (1 - T)) *
        rightTensor (ι₁ := ι)
          (((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) * W gb.1))
  have hraw_eq :
      gCommStabilityTwoRawScalarDefect params strategy family G x =
        avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, t vy gb) := by
    unfold gCommStabilityTwoRawScalarDefect
    change avgOver 𝒟V (fun vy =>
        avgOver 𝒟U (fun u =>
          ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((G x).outcome g *
                    (evaluatedPointFamily params family vy).outcome b *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  (((strategy.pointMeasurement vy).toSubMeas.outcome b) *
                    ((strategy.pointMeasurement
                      (appendPoint params u x)).toSubMeas.outcome (g u)))))) =
      avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, t vy gb)
    apply congrArg (avgOver 𝒟V)
    funext vy
    let L : Polynomial params → Fq params → MIPStarRE.Quantum.Op ι := fun g b =>
      (G x).outcome g * (evaluatedPointFamily params family vy).outcome b * (1 - (G x).total)
    let P : Fq params → MIPStarRE.Quantum.Op ι := fun b =>
      (strategy.pointMeasurement vy).toSubMeas.outcome b
    let Q : Point params → Polynomial params → MIPStarRE.Quantum.Op ι := fun u g =>
      (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u)
    have hW :
        ∀ g : Polynomial params,
          averageOperatorOverDistribution 𝒟U (fun u => Q u g) = W g := by
      intro g
      rfl
    calc
      avgOver 𝒟U (fun u =>
          ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((G x).outcome g *
                    (evaluatedPointFamily params family vy).outcome b *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  (((strategy.pointMeasurement vy).toSubMeas.outcome b) *
                    ((strategy.pointMeasurement
                      (appendPoint params u x)).toSubMeas.outcome (g u)))))
        = ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (L g b) *
                rightTensor (ι₁ := ι)
                  (P b * averageOperatorOverDistribution 𝒟U (fun u => Q u g))) := by
            simpa [L, P, Q] using
              (avgOver_right_linear (ι := ι) 𝒟U strategy.state L P Q)
      _ = ∑ gb : Polynomial params × Fq params, t vy gb := by
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro g _
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [hW g]
  have hT_herm : Tᴴ = T := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [T] using (G x).total_nonneg).isHermitian.eq
  have hTc_herm : (1 - T)ᴴ = 1 - T := by simp [hT_herm]
  have hGproj : ∀ g : Polynomial params, (G x).outcome g * (G x).outcome g = (G x).outcome g := by
    intro g
    simpa [hG x] using (family.meas x).proj g
  have hX_expand : ∀ vy gb,
      X vy gb * (X vy gb)ᴴ =
        leftTensor (ι₂ := ι) ((G x).outcome gb.1) *
          rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) := by
    intro vy gb
    have hG_herm : ((G x).outcome gb.1)ᴴ = (G x).outcome gb.1 :=
      (G x).outcome_hermitian gb.1
    have hP_herm : ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2)ᴴ =
        (strategy.pointMeasurement vy).toSubMeas.outcome gb.2 :=
      ((strategy.pointMeasurement vy).toSubMeas.outcome_hermitian gb.2)
    have hP_proj : (strategy.pointMeasurement vy).toSubMeas.outcome gb.2 *
        (strategy.pointMeasurement vy).toSubMeas.outcome gb.2 =
        (strategy.pointMeasurement vy).toSubMeas.outcome gb.2 := by
      simpa using (strategy.pointMeasurement vy).proj gb.2
    calc
      X vy gb * (X vy gb)ᴴ
        = (opTensor ((G x).outcome gb.1)
            ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2)) *
          (opTensor ((G x).outcome gb.1)
            ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2))ᴴ := by
            simp [X, leftTensor_mul_rightTensor_eq_opTensor]
      _ = opTensor (((G x).outcome gb.1) * ((G x).outcome gb.1))
            (((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) *
              ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2)) := by
            rw [conjTranspose_opTensor, opTensor_mul]
            simp [hG_herm, hP_herm]
      _ = leftTensor (ι₂ := ι) ((G x).outcome gb.1) *
            rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) := by
            rw [hGproj gb.1, hP_proj, leftTensor_mul_rightTensor_eq_opTensor]
  have hY_le : ∀ vy gb,
      ev strategy.state ((Y vy gb)ᴴ * Y vy gb) ≤ yDiag vy gb := by
    intro vy gb
    let B : MIPStarRE.Quantum.Op ι := (evaluatedPointFamily params family vy).outcome gb.2
    let Gg : MIPStarRE.Quantum.Op ι := (G x).outcome gb.1
    let Wg : MIPStarRE.Quantum.Op ι := W gb.1
    have hG_herm : Ggᴴ = Gg := by simpa [Gg] using (G x).outcome_hermitian gb.1
    have hB_herm : Bᴴ = B := by
      simpa [B] using (evaluatedPointFamily params family vy).outcome_hermitian gb.2
    have hW_herm : Wgᴴ = Wg := by
      simpa [Wg, W] using
        averagedSlicePointEvaluationOperator_hermitian params strategy x gb.1
    have hGg_proj : Gg * Gg = Gg := by
      simpa [Gg] using hGproj gb.1
    have hleft_alg :
        ((1 - T) * B * Gg) * (Gg * B * (1 - T)) =
          (1 - T) * (B * Gg * B) * (1 - T) := by
      calc
        ((1 - T) * B * Gg) * (Gg * B * (1 - T))
            = (1 - T) * B * (Gg * Gg) * B * (1 - T) := by noncomm_ring
        _ = (1 - T) * B * Gg * B * (1 - T) := by rw [hGg_proj]
        _ = (1 - T) * (B * Gg * B) * (1 - T) := by noncomm_ring
    have hY_expand :
        (Y vy gb)ᴴ * Y vy gb =
          leftTensor (ι₂ := ι) ((1 - T) * (B * Gg * B) * (1 - T)) *
            rightTensor (ι₁ := ι) (Wg * Wg) := by
      calc
        (Y vy gb)ᴴ * Y vy gb
          = (opTensor (Gg * B * (1 - T)) Wg)ᴴ *
              opTensor (Gg * B * (1 - T)) Wg := by
              simp [Y, Gg, B, Wg, leftTensor_mul_rightTensor_eq_opTensor]
        _ = opTensor (((Gg * B * (1 - T))ᴴ) * (Gg * B * (1 - T)))
              (Wgᴴ * Wg) := by
              rw [conjTranspose_opTensor, opTensor_mul]
        _ = opTensor (((1 - T) * B * Gg) * (Gg * B * (1 - T))) (Wg * Wg) := by
              simp [Matrix.conjTranspose_mul, hG_herm, hB_herm, hTc_herm, hW_herm,
                mul_assoc]
        _ = opTensor ((1 - T) * (B * Gg * B) * (1 - T)) (Wg * Wg) := by
              rw [hleft_alg]
        _ = leftTensor (ι₂ := ι) ((1 - T) * (B * Gg * B) * (1 - T)) *
              rightTensor (ι₁ := ι) (Wg * Wg) := by
              rw [leftTensor_mul_rightTensor_eq_opTensor]
    have hleft_pos : 0 ≤ (1 - T) * (B * Gg * B) * (1 - T) := by
      have hBGpos : 0 ≤ B * Gg * B := by
        exact IsSelfAdjoint.conjugate_nonneg (by simpa [Gg] using (G x).outcome_pos gb.1) hB_herm
      exact IsSelfAdjoint.conjugate_nonneg hBGpos hTc_herm
    have hWsq_le : Wg * Wg ≤ family.witness x := by
      calc
        Wg * Wg ≤ Wg := by
          simpa [Wg, W] using
            averagedSlicePointEvaluationOperator_sq_le_self params strategy x gb.1
        _ ≤ family.witness x := by
          simpa [Wg, W] using hbound.averagedPoint_le_witness x gb.1
    calc
      ev strategy.state ((Y vy gb)ᴴ * Y vy gb)
        = ev strategy.state
            (leftTensor (ι₂ := ι) ((1 - T) * (B * Gg * B) * (1 - T)) *
              rightTensor (ι₁ := ι) (Wg * Wg)) := by rw [hY_expand]
      _ ≤ ev strategy.state
            (leftTensor (ι₂ := ι) ((1 - T) * (B * Gg * B) * (1 - T)) *
              rightTensor (ι₁ := ι) (family.witness x)) := by
            exact ev_mono strategy.state _ _ <| by
              rw [leftTensor_mul_rightTensor_eq_opTensor,
                leftTensor_mul_rightTensor_eq_opTensor]
              exact MIPStarRE.LDT.opTensor_mono_right hleft_pos hWsq_le
      _ = yDiag vy gb := by
            simp [yDiag, B, Gg, T]
  have ht : ∀ vy gb, |t vy gb| ≤ Real.sqrt (xDiag vy gb) * Real.sqrt (yDiag vy gb) := by
    intro vy gb
    have hXY :
        X vy gb * Y vy gb =
          leftTensor (ι₂ := ι)
            ((G x).outcome gb.1 *
              (evaluatedPointFamily params family vy).outcome gb.2 * (1 - T)) *
            rightTensor (ι₁ := ι)
              (((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) * W gb.1) := by
      calc
        X vy gb * Y vy gb
          = opTensor ((G x).outcome gb.1)
              ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) *
            opTensor
              ((G x).outcome gb.1 *
                (evaluatedPointFamily params family vy).outcome gb.2 * (1 - T))
              (W gb.1) := by
              simp [X, Y, leftTensor_mul_rightTensor_eq_opTensor]
        _ = opTensor
              (((G x).outcome gb.1 * (G x).outcome gb.1) *
                (evaluatedPointFamily params family vy).outcome gb.2 * (1 - T))
              (((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) * W gb.1) := by
              rw [opTensor_mul]
              simp [mul_assoc]
        _ = leftTensor (ι₂ := ι)
              ((G x).outcome gb.1 *
                (evaluatedPointFamily params family vy).outcome gb.2 * (1 - T)) *
              rightTensor (ι₁ := ι)
                (((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) * W gb.1) := by
              rw [hGproj gb.1, leftTensor_mul_rightTensor_eq_opTensor]
    have hbase := ev_abs_mul_le_sqrt strategy.state (X vy gb) (Y vy gb)
    calc
      |t vy gb| = |ev strategy.state (X vy gb * Y vy gb)| := by
        rw [hXY]
      _ ≤ Real.sqrt (xDiag vy gb) *
          Real.sqrt (ev strategy.state ((Y vy gb)ᴴ * Y vy gb)) := by
            simpa [xDiag] using hbase
      _ ≤ Real.sqrt (xDiag vy gb) * Real.sqrt (yDiag vy gb) := by
            exact mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt (hY_le vy gb)) (Real.sqrt_nonneg _)
  have hx : ∀ vy gb, 0 ≤ xDiag vy gb := by
    intro vy gb
    simpa [xDiag] using ev_adjoint_self_nonneg strategy.state ((X vy gb)ᴴ)
  have hy : ∀ vy gb, 0 ≤ yDiag vy gb := by
    intro vy gb
    let B : MIPStarRE.Quantum.Op ι := (evaluatedPointFamily params family vy).outcome gb.2
    let Gg : MIPStarRE.Quantum.Op ι := (G x).outcome gb.1
    have hB_herm : Bᴴ = B := by
      simpa [B] using (evaluatedPointFamily params family vy).outcome_hermitian gb.2
    have hleft_pos : 0 ≤ (1 - T) * (B * Gg * B) * (1 - T) := by
      have hBGpos : 0 ≤ B * Gg * B := by
        exact IsSelfAdjoint.conjugate_nonneg (by simpa [Gg] using (G x).outcome_pos gb.1) hB_herm
      exact IsSelfAdjoint.conjugate_nonneg hBGpos hTc_herm
    unfold yDiag
    apply ev_nonneg_of_psd
    rw [leftTensor_mul_rightTensor_eq_opTensor]
    simpa [B, Gg, T, opTensor] using
      MIPStarRE.Quantum.kronecker_nonneg hleft_pos (hbound.sliceOpPSD x)
  have hfirst_point : ∀ vy : Point params.next,
      ∑ gb : Polynomial params × Fq params, xDiag vy gb =
        ev strategy.state
          (leftTensor (ι₂ := ι) ((G x).total) *
            rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
    intro vy
    calc
      ∑ gb : Polynomial params × Fq params, xDiag vy gb
        = ∑ gb : Polynomial params × Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι) ((G x).outcome gb.1) *
                rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2)) := by
            refine Finset.sum_congr rfl ?_
            intro gb _
            change ev strategy.state (X vy gb * (X vy gb)ᴴ) =
              ev strategy.state
                (leftTensor (ι₂ := ι) ((G x).outcome gb.1) *
                  rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2))
            rw [hX_expand vy gb]
      _ = ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι) ((G x).outcome g) *
                rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome b)) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ g : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) ((G x).outcome g) *
                rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
            refine Finset.sum_congr rfl ?_
            intro g _
            calc
              ∑ b : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι) ((G x).outcome g) *
                    rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome b))
                = ev strategy.state
                    (leftTensor (ι₂ := ι) ((G x).outcome g) *
                      rightTensor (ι₁ := ι)
                        (∑ b : Fq params, (strategy.pointMeasurement vy).outcome b)) := by
                    simp [ev_finset_sum, ← rightTensor_finset_sum, Finset.mul_sum]
              _ = ev strategy.state
                    (leftTensor (ι₂ := ι) ((G x).outcome g) *
                      rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
                    have hsumP :
                        (∑ b : Fq params, (strategy.pointMeasurement vy).outcome b) =
                          (1 : MIPStarRE.Quantum.Op ι) := by
                      exact (strategy.pointMeasurement vy).toMeasurement.sum_eq
                    rw [hsumP]
      _ = ev strategy.state
            (leftTensor (ι₂ := ι) ((G x).total) *
              rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
            calc
              ∑ g : Polynomial params,
                ev strategy.state
                  (leftTensor (ι₂ := ι) ((G x).outcome g) *
                    rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι))
                = ev strategy.state
                    ((∑ g : Polynomial params, leftTensor (ι₂ := ι) ((G x).outcome g)) *
                      rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
                    simp [ev_finset_sum, Finset.sum_mul]
              _ = ev strategy.state
                  (leftTensor (ι₂ := ι) ((G x).total) *
                    rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
                    rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ
                      (fun g : Polynomial params => (G x).outcome g), (G x).sum_eq_total]
  have hfirst : avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, xDiag vy gb) ≤ 1 := by
    calc
      avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, xDiag vy gb)
        = ev strategy.state
            (leftTensor (ι₂ := ι) ((G x).total) *
              rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
            calc
              avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, xDiag vy gb)
                = avgOver 𝒟V (fun _ : Point params.next =>
                    ev strategy.state
                      (leftTensor (ι₂ := ι) ((G x).total) *
                        rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι))) := by
                    apply congrArg (avgOver 𝒟V)
                    funext vy
                    exact hfirst_point vy
              _ = ev strategy.state
                    (leftTensor (ι₂ := ι) ((G x).total) *
                      rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
                    simpa [𝒟V] using
                      (avgOver_uniform_const (α := Point params.next)
                        (ev strategy.state
                          (leftTensor (ι₂ := ι) ((G x).total) *
                            rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι))))
      _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
            exact ev_mono strategy.state _ _ <| by
              rw [rightTensor_one (ι₁ := ι) (ι₂ := ι), mul_one]
              exact leftTensor_le_one (ι₂ := ι) (G x).total_le_one
      _ = 1 := ev_one_of_isNormalized strategy.state hnorm
  have hsecond_point : ∀ vy : Point params.next,
      (∑ gb : Polynomial params × Fq params, yDiag vy gb) ≤ hbound.storedResidual G x := by
    intro vy
    calc
      ∑ gb : Polynomial params × Fq params, yDiag vy gb
        = ev strategy.state
            (leftTensor (ι₂ := ι)
              (∑ gb : Polynomial params × Fq params,
                ((1 - (G x).total) *
                  ((evaluatedPointFamily params family vy).outcome gb.2 *
                    (G x).outcome gb.1 *
                    (evaluatedPointFamily params family vy).outcome gb.2) *
                  (1 - (G x).total))) *
              rightTensor (ι₁ := ι) (family.witness x)) := by
            simpa [yDiag, T] using
              (sum_ev_leftTensor_mul_rightTensor_const
                (ι := ι) (Finset.univ : Finset (Polynomial params × Fq params))
                strategy.state
                (fun gb : Polynomial params × Fq params =>
                  ((1 - (G x).total) *
                    ((evaluatedPointFamily params family vy).outcome gb.2 *
                      (G x).outcome gb.1 *
                      (evaluatedPointFamily params family vy).outcome gb.2) *
                    (1 - (G x).total)))
                (family.witness x))
      _ ≤ ev strategy.state
            (leftTensor (ι₂ := ι) (1 - (G x).total) *
              rightTensor (ι₁ := ι) (family.witness x)) := by
            exact ev_mono strategy.state _ _ <| by
              rw [leftTensor_mul_rightTensor_eq_opTensor,
                leftTensor_mul_rightTensor_eq_opTensor]
              exact opTensor_mono_left
                (gCommStabilityTwo_raw_left_sum_le params family G hG x vy)
                (hbound.sliceOpPSD x)
      _ = hbound.storedResidual G x := rfl
  have hsecond :
      avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, yDiag vy gb) ≤
        hbound.storedResidual G x := by
    calc
      avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, yDiag vy gb)
        ≤ avgOver 𝒟V (fun _ : Point params.next => hbound.storedResidual G x) := by
            exact avgOver_mono 𝒟V _ _ hsecond_point
      _ = hbound.storedResidual G x := by
            simpa [𝒟V] using
              (avgOver_uniform_const (α := Point params.next) (hbound.storedResidual G x))
  have hcs :=
    MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz
      (𝒟 := 𝒟V) (t := t) (x := xDiag) (y := yDiag) ht hx hy
  calc
    |gCommStabilityTwoRawScalarDefect params strategy family G x|
      = |avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, t vy gb)| := by
          rw [hraw_eq]
    _ ≤
        Real.sqrt (avgOver 𝒟V
          (fun vy => ∑ gb : Polynomial params × Fq params, xDiag vy gb)) *
          Real.sqrt (avgOver 𝒟V
            (fun vy => ∑ gb : Polynomial params × Fq params, yDiag vy gb)) := hcs
    _ ≤ Real.sqrt 1 * Real.sqrt (hbound.storedResidual G x) := by
          apply mul_le_mul
          · exact Real.sqrt_le_sqrt hfirst
          · exact Real.sqrt_le_sqrt hsecond
          · exact Real.sqrt_nonneg _
          · exact Real.sqrt_nonneg _
    _ = Real.sqrt (hbound.storedResidual G x) := by simp



end MIPStarRE.LDT.Commutativity

end

end LIDT

open LIDT
/-!
# Section 11 commutativity: raw second scalar stability bound

The raw uncollapsed form of the second scalar stability estimate.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open GCommStability.Scalar
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hnorm : strategy.state.IsNormalized)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (G : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    |_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.gCommStabilityTwoRawScalarDefect params strategy family G)| ≤ Real.sqrt zeta := by
  have h𝒟 :
      ∑ x ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)).support,
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)).weight x ≤ 1 := by
    simpa using _root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Fq params)
  calc
    |_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.gCommStabilityTwoRawScalarDefect params strategy family G)|
      ≤ Real.sqrt
          (_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
            (fun x => hbound.storedResidual G x)) := by
          exact
            _root_.LIDT.MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.gCommStabilityTwoRawScalarDefect params strategy family G)
              (fun x => hbound.storedResidual G x)
              (gCommStabilityTwo_raw_scalar_pointwise_bound
                params strategy zeta hnorm family G hG hbound)
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar.storedResidual_nonneg
                params strategy family G zeta hbound)
              h𝒟
    _ ≤ Real.sqrt zeta := by
          exact Real.sqrt_le_sqrt <|
            hbound.storedBoundedResidualBound G hG
