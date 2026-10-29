-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar.scalar_pointwise_cauchy_schwarz_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:47:23.772818+00:00
-- url     : https://prove2.me/submissions/3cacf9eb-a1d5-446c-9bb7-b0f6d2183d83

-- Generated proof for MIPStarRE.LDT.Commutativity.GCommStability.Scalar.scalar_pointwise_cauchy_schwarz_bound.
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




end GCommStability.Scalar

end MIPStarRE.LDT.Commutativity

end

/- Source helpers from MIPStarRE/LDT/Commutativity/Scaffold/Products.lean. -/
/-!
# Section 11 commutativity: product estimates

Basic product-style lemmas on projective submeasurement outcomes — in
particular orthogonality of distinct outcomes — reused throughout the
Section 11 commutativity argument.

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





/-- The positive square root of a submeasurement outcome squares back to that
outcome. -/
lemma sqrt_subMeas_outcome_mul_self
    {α : Type*} [Fintype α]
    (A : SubMeas α ι) (a : α) :
    CFC.sqrt (A.outcome a) * CFC.sqrt (A.outcome a) = A.outcome a := by
  simpa using CFC.sqrt_mul_sqrt_self (A.outcome a) (A.outcome_pos a)































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

end LIDT

open LIDT
/-!
# Section 11 commutativity: shared scalar stability helpers

Auxiliary positivity, order, and bounded-residual lemmas used by the scalar stability estimates.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (G : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (R : _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ι)
    (x : _root_.LIDT.MIPStarRE.LDT.Fq params)
    (hfirstR :
      ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (R.outcome g)) ≤ 1) :
    |∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (R.outcome g * (1 - (G x).total)) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (_root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g))|
      ≤ Real.sqrt (hbound.storedResidual G x) := by
  let T : _root_.LIDT.MIPStarRE.Quantum.Op ι := (G x).total
  let W : _root_.LIDT.MIPStarRE.LDT.Polynomial params → _root_.LIDT.MIPStarRE.Quantum.Op ι :=
    _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x
  let X : _root_.LIDT.MIPStarRE.LDT.Polynomial params → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun g =>
    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (CFC.sqrt (R.outcome g))
  let Y : _root_.LIDT.MIPStarRE.LDT.Polynomial params → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun g =>
    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (CFC.sqrt (R.outcome g) * (1 - T)) *
      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (W g)
  have hT_herm : Tᴴ = T := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [T] using (G x).total_nonneg).isHermitian.eq
  have hTc_herm : (1 - T)ᴴ = 1 - T := by simp [hT_herm]
  have hT_proj : T * T = T := by
    simpa [T, hG] using
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj (family.meas x)
  have hX_expand :
      ∀ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
        X g * (X g)ᴴ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (R.outcome g) := by
    intro g
    have hsqrt_herm : (CFC.sqrt (R.outcome g))ᴴ = CFC.sqrt (R.outcome g) :=
      (Matrix.nonneg_iff_posSemidef.mp
        (CFC.sqrt_nonneg (R.outcome g))).isHermitian.eq
    calc
      X g * (X g)ᴴ
          = _root_.LIDT.MIPStarRE.LDT.opTensor (CFC.sqrt (R.outcome g)) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) *
              (_root_.LIDT.MIPStarRE.LDT.opTensor (CFC.sqrt (R.outcome g)) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))ᴴ := by
                simp [X, _root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor]
      _ = _root_.LIDT.MIPStarRE.LDT.opTensor (CFC.sqrt (R.outcome g)) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) *
            _root_.LIDT.MIPStarRE.LDT.opTensor (CFC.sqrt (R.outcome g)) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := by
              rw [_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor]
              simp [hsqrt_herm]
      _ = _root_.LIDT.MIPStarRE.LDT.opTensor
            (CFC.sqrt (R.outcome g) * CFC.sqrt (R.outcome g))
            (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := by
              rw [_root_.LIDT.MIPStarRE.LDT.opTensor_mul]
              simp
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (R.outcome g) := by
              rw [_root_.LIDT.MIPStarRE.LDT.Commutativity.sqrt_subMeas_outcome_mul_self R g]
  have hY_expand :
      ∀ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
        (Y g)ᴴ * Y g =
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (W g * W g) := by
    intro g
    have hsqrt_herm : (CFC.sqrt (R.outcome g))ᴴ = CFC.sqrt (R.outcome g) :=
      (Matrix.nonneg_iff_posSemidef.mp
        (CFC.sqrt_nonneg (R.outcome g))).isHermitian.eq
    have hW_herm : (W g)ᴴ = W g :=
      _root_.LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar.averagedSlicePointEvaluationOperator_hermitian params strategy x g
    calc
      (Y g)ᴴ * Y g
          = (_root_.LIDT.MIPStarRE.LDT.opTensor (CFC.sqrt (R.outcome g) * (1 - T)) (W g))ᴴ *
              _root_.LIDT.MIPStarRE.LDT.opTensor (CFC.sqrt (R.outcome g) * (1 - T)) (W g) := by
                simp [Y, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
      _ = _root_.LIDT.MIPStarRE.LDT.opTensor (((CFC.sqrt (R.outcome g) * (1 - T))ᴴ) *
            (CFC.sqrt (R.outcome g) * (1 - T))) ((W g)ᴴ * W g) := by
              rw [_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor, _root_.LIDT.MIPStarRE.LDT.opTensor_mul]
      _ = _root_.LIDT.MIPStarRE.LDT.opTensor (((1 - T) *
              ((CFC.sqrt (R.outcome g) * CFC.sqrt (R.outcome g)) * (1 - T))))
            (W g * W g) := by
              simp [Matrix.conjTranspose_mul, hsqrt_herm, hTc_herm, hW_herm, mul_assoc]
      _ = _root_.LIDT.MIPStarRE.LDT.opTensor (((1 - T) * R.outcome g * (1 - T))) (W g * W g) := by
              rw [_root_.LIDT.MIPStarRE.LDT.Commutativity.sqrt_subMeas_outcome_mul_self R g]
              simp [mul_assoc]
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (W g * W g) := by
              rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
  have hfirst :
      ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.ev strategy.state (X g * (X g)ᴴ) ≤ 1 := by
    calc
      ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.ev strategy.state (X g * (X g)ᴴ)
        = ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (R.outcome g)) := by
              refine Finset.sum_congr rfl ?_
              intro g _
              rw [hX_expand g]
      _ ≤ 1 := hfirstR
  have hsecond :
      ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.ev strategy.state ((Y g)ᴴ * Y g) ≤
        hbound.storedResidual G x := by
    have hsum_eq :
        ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (family.witness x))
          = _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((1 - T) * R.total * (1 - T))) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (family.witness x)) := by
      have hsum_inner :
          ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ((1 - T) * R.outcome g * (1 - T)) =
            (1 - T) * R.total * (1 - T) := by
        calc
          ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ((1 - T) * R.outcome g * (1 - T))
            = (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, (1 - T) * R.outcome g) * (1 - T) := by
                rw [Finset.sum_mul]
          _ = ((1 - T) * ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, R.outcome g) * (1 - T) := by
                rw [Matrix.mul_sum]
          _ = (1 - T) * R.total * (1 - T) := by
                rw [R.sum_eq_total]
      calc
        ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (family.witness x))
          = _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (family.witness x)) := by
                    rw [← _root_.LIDT.MIPStarRE.LDT.ev_sum strategy.state]
        _ = _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((1 - T) * R.total * (1 - T))) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (family.witness x)) := by
              congr 1
              calc
                ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
                    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (family.witness x)
                  = (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
                      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T)))) *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (family.witness x) := by
                        rw [Finset.sum_mul]
                _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ((1 - T) * R.outcome g * (1 - T))) *
                        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (family.witness x) := by
                        rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ
                          (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => ((1 - T) * R.outcome g * (1 - T)))]
                _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((1 - T) * R.total * (1 - T))) *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (family.witness x) := by
                        rw [hsum_inner]
    calc
      ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.ev strategy.state ((Y g)ᴴ * Y g)
        = ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (W g * W g)) := by
              refine Finset.sum_congr rfl ?_
              intro g _
              rw [hY_expand g]
      _ ≤ ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (W g)) := by
              refine Finset.sum_le_sum ?_
              intro g _
              exact _root_.LIDT.MIPStarRE.LDT.ev_mono strategy.state _ _ <| by
                rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor,
                  _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
                exact _root_.LIDT.MIPStarRE.LDT.opTensor_mono_right
                  (IsSelfAdjoint.conjugate_nonneg (R.outcome_pos g) hTc_herm)
                  (_root_.LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar.averagedSlicePointEvaluationOperator_sq_le_self params strategy x g)
      _ ≤ ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (family.witness x)) := by
              refine Finset.sum_le_sum ?_
              intro g _
              exact _root_.LIDT.MIPStarRE.LDT.ev_mono strategy.state _ _ <| by
                rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor,
                  _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
                exact _root_.LIDT.MIPStarRE.LDT.opTensor_mono_right
                  (IsSelfAdjoint.conjugate_nonneg (R.outcome_pos g) hTc_herm)
                  (hbound.averagedPoint_le_witness x g)
      _ = _root_.LIDT.MIPStarRE.LDT.ev strategy.state
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((1 - T) * R.total * (1 - T))) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (family.witness x)) := hsum_eq
      _ ≤ _root_.LIDT.MIPStarRE.LDT.ev strategy.state
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (1 - T) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (family.witness x)) := by
            apply _root_.LIDT.MIPStarRE.LDT.ev_mono strategy.state _ _
            rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor,
              _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
            exact _root_.LIDT.MIPStarRE.LDT.opTensor_mono_left
              (by
                calc
                  ((1 - T) * R.total * (1 - T)) ≤ (1 - T) * 1 * (1 - T) := by
                    exact IsSelfAdjoint.conjugate_le_conjugate R.total_le_one hTc_herm
                  _ = 1 - T := by
                    calc
                      (1 - T) * 1 * (1 - T) = (1 - T) * (1 - T) := by simp
                      _ = 1 - T - T + T * T := by noncomm_ring
                      _ = 1 - T := by simp [hT_proj])
              (hbound.sliceOpPSD x)
      _ = hbound.storedResidual G x := by
            rfl
  have hcs := _root_.LIDT.MIPStarRE.LDT.Preliminaries.sum_ev_mul_le_sqrt strategy.state X Y
  have hXY :
      ∀ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
        X g * Y g = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (R.outcome g * (1 - T)) *
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (W g) := by
    intro g
    calc
      X g * Y g
          = _root_.LIDT.MIPStarRE.LDT.opTensor (CFC.sqrt (R.outcome g)) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) *
              _root_.LIDT.MIPStarRE.LDT.opTensor (CFC.sqrt (R.outcome g) * (1 - T)) (W g) := by
                simp [X, Y, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
      _ = _root_.LIDT.MIPStarRE.LDT.opTensor
            ((CFC.sqrt (R.outcome g) * CFC.sqrt (R.outcome g)) * (1 - T))
            (W g) := by
              rw [_root_.LIDT.MIPStarRE.LDT.opTensor_mul]
              simp [mul_assoc]
      _ = _root_.LIDT.MIPStarRE.LDT.opTensor (R.outcome g * (1 - T)) (W g) := by
              rw [_root_.LIDT.MIPStarRE.LDT.Commutativity.sqrt_subMeas_outcome_mul_self R g]
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (R.outcome g * (1 - T)) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (W g) := by
              rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
  calc
    |∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (R.outcome g * (1 - T)) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (W g))|
      = |∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.ev strategy.state (X g * Y g)| := by
          refine congrArg abs ?_
          refine Finset.sum_congr rfl ?_
          intro g _
          rw [hXY g]
    _ ≤ Real.sqrt (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.ev strategy.state (X g * (X g)ᴴ)) *
          Real.sqrt (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.ev strategy.state ((Y g)ᴴ * Y g)) := hcs
    _ ≤ Real.sqrt 1 * Real.sqrt (hbound.storedResidual G x) := by
          apply mul_le_mul
          · exact Real.sqrt_le_sqrt hfirst
          · exact Real.sqrt_le_sqrt hsecond
          · exact Real.sqrt_nonneg _
          · exact Real.sqrt_nonneg _
    _ = Real.sqrt (hbound.storedResidual G x) := by simp
