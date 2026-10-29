-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseSix_first_reverse_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:54:09.733835+00:00
-- url     : https://prove2.me/submissions/aeacf0b4-0118-41e7-8528-91c828892271

-- Generated proof for MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseSix_first_reverse_bound.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_leftRightTensor_prefix_pointMeasurement_adjoint_normalization

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainBasic/Normalization.lean. -/
/-!
# Tensor normalization helpers for the evaluated-slice paper chain

This file contains the normalization estimates used as side conditions for
`closenessOfIP` and its adjoint form in the scalar approximation chain.
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]









/-- The total projector of a projective submeasurement absorbs each outcome on the left. -/
lemma projSubMeas_total_mul_outcome_eq_outcome
    {α : Type*} [Fintype α] (A : ProjSubMeas α ι) (a : α) :
    A.total * A.outcome a = A.outcome a := by
  have hright := MIPStarRE.LDT.Preliminaries.projSubMeas_outcome_mul_total_eq_outcome A a
  have htotal_herm : A.totalᴴ = A.total :=
    (Matrix.nonneg_iff_posSemidef.mp A.total_nonneg).isHermitian.eq
  have h := congrArg Matrix.conjTranspose hright
  simpa [Matrix.conjTranspose_mul, A.outcome_hermitian a, htotal_herm] using h



end MIPStarRE.LDT.Commutativity

end

/- Source helpers from MIPStarRE/LDT/Preliminaries/CauchySchwarz.lean. -/
/-!
# Cauchy–Schwarz Inequalities for Approximate Measurements

Formalizes Cauchy–Schwarz-style propositions from Section 3
(Preliminaries) of the LDT paper:
- `easyApproxFromApproxDelta` — Proposition `prop:easy-approx-from-approx-delta`
- `closenessOfIP` / `closenessOfIPAdjoint` — Proposition `prop:closeness-of-ip`
  (`eq:closeness3` / `eq:closeness4`)
- `cabApproxDelta` — Proposition `prop:cab-approx-delta`

## References

- `references/ldt-paper/preliminaries.tex`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT









/-- `prop:closeness-of-ip` (`eq:closeness4`, adjoint version).

If `A† ≈_γ B†` and `Σ_a (Σ_b C_{a,b})†(Σ_b C_{a,b}) ≤ I`, then
`|𝔼_x Σ_{a,b} ⟨ψ| A_a C_{a,b} |ψ⟩ -
  𝔼_x Σ_{a,b} ⟨ψ| B_a C_{a,b} |ψ⟩| ≤ √γ`. -/
theorem closenessOfIPAdjoint
    {Question OutcomeA OutcomeB : Type*} {ι : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (γ : Error)
    (hAB :
      avgOver 𝒟
        (fun q => qSDDCore ψ (fun a => (A q a)ᴴ) (fun a => (B q a)ᴴ)) ≤ γ)
    (hC :
      ∀ q,
        ∑ a : OutcomeA,
          (∑ b : OutcomeB, C q a b)ᴴ * (∑ b : OutcomeB, C q a b) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A q a * C q a b)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B q a * C q a b))| ≤
      Real.sqrt γ := by
  simpa using closenessOfInnerProduct_right ψ hψ 𝒟 h𝒟 A B C γ hAB hC



end MIPStarRE.LDT.Preliminaries

end

end LIDT

open LIDT
/-!
# Phase-six reverse insertion for the evaluated-slice paper chain

This file proves the first reverse `eq:add-an-a` bound used after the
paper line-87 phase-five removal.
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
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hnorm : strategy.state.IsNormalized)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (hcombined_fst : _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
      (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft params family q.1)
      (fun q =>
        (_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy) q.1))
      (4 * zeta)) :
    let 𝒟 := _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)
    let phase5PaperRemoved : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error :=
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperRemoved params strategy family
    let phase6FirstRemoved : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error :=
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseSixFirstRemoved params strategy family
    |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase5PaperRemoved - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase6FirstRemoved| ≤
      2 * Real.sqrt zeta := by
  let 𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params) :=
    _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)
  let pointMeas : _root_.LIDT.MIPStarRE.LDT.IdxMeas (_root_.LIDT.MIPStarRE.LDT.Point params.next) (_root_.LIDT.MIPStarRE.LDT.Fq params) ι :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy
  let phase5PaperRemoved : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperRemoved params strategy family
  let phase6FirstReverse : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseSixFirstReverse params strategy family
  let phase6FirstRemoved : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseSixFirstRemoved params strategy family
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using
      _root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)
  let Aop : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a => _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a)
  let Bop : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a =>
      ((_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy) q.1).outcome a)
  let C : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.Fq params →
      _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun q a b =>
    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
        (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
          ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b)) *
      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
        ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b)
  have hAop_herm : ∀ q a, (Aop q a)ᴴ = Aop q a := by
    intro q a
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (_root_.LIDT.MIPStarRE.LDT.leftTensor_nonneg (ι₂ := ι)
          ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome_pos a))).isHermitian.eq
  have hBop_herm : ∀ q a, (Bop q a)ᴴ = Bop q a := by
    intro q a
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        ((_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy) q.1).outcome_pos a)).isHermitian.eq
  have hAB :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q =>
        _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (fun a => (Aop q a)ᴴ) (fun a => (Bop q a)ᴴ)) ≤
        4 * zeta := by
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q =>
          _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (fun a => (Aop q a)ᴴ) (fun a => (Bop q a)ᴴ))
          = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (Aop q) (Bop q)) := by
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            intro q
            simp only [_root_.LIDT.MIPStarRE.LDT.qSDDCore, hAop_herm q, hBop_herm q]
      _ ≤ 4 * zeta := by
          have hbound := hcombined_fst.squaredDistanceBound
          change _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (Aop q) (Bop q)) ≤
            4 * zeta at hbound
          exact hbound
  have hC :
      ∀ q,
        ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, (∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, C q a b)ᴴ * (∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, C q a b) ≤ 1 := by
    intro q
    simpa [C, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas, _root_.LIDT.MIPStarRE.LDT.Parameters.next] using
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.leftRightTensor_prefix_pointMeasurement_adjoint_normalization
        (A := _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q)
        (B := _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q)
        (R := strategy.pointMeasurement q.2))
  have hreverse_norm :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase6FirstReverse =
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
          _root_.LIDT.MIPStarRE.LDT.ev strategy.state (Aop q a * C q a b)) := by
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro q
    dsimp [phase6FirstReverse, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseSixFirstReverse, Aop, C]
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    congr 1
    rw [← mul_assoc, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor, mul_assoc]
  have hpaper_norm :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase5PaperRemoved =
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
          _root_.LIDT.MIPStarRE.LDT.ev strategy.state (Bop q a * C q a b)) := by
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro q
    dsimp [phase5PaperRemoved, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperRemoved, Bop, C]
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    congr 1
    have htotal_left :
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).total *
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a =
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a := by
      simpa [_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstProj] using
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.projSubMeas_total_mul_outcome_eq_outcome
          (A := _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstProj params family q) a)
    have htotal_left' :
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family q.1).total *
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a =
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a := by
      simpa [_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor] using htotal_left
    have htotal_prod :
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family q.1).total *
            ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a *
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) =
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a *
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b := by
      rw [← mul_assoc, htotal_left']
    calc
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a *
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
            ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome a *
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b)
        = _root_.LIDT.MIPStarRE.LDT.opTensor
            ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a *
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b)
            ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome a *
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b) := by
            rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
      _ = _root_.LIDT.MIPStarRE.LDT.opTensor
            ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family q.1).total *
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a *
                (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b))
            ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome a *
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b) := by
            exact (congrArg
              (fun X => _root_.LIDT.MIPStarRE.LDT.opTensor X
                ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome a *
                  (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b)) htotal_prod).symm
      _ = (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family q.1).total *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome a)) *
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a *
                (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome b)) := by
            rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor,
              _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor, _root_.LIDT.MIPStarRE.LDT.opTensor_mul]
  have hproject :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase6FirstReverse = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase6FirstRemoved := by
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro q
    dsimp [phase6FirstReverse, phase6FirstRemoved,
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseSixFirstReverse, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseSixFirstRemoved]
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    have hAproj :
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a *
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a =
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a := by
      simpa [_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor] using
        _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily_outcome_proj params family q.1 a
    simp [hAproj]
  have hclose :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.closenessOfIPAdjoint
      strategy.state hnorm 𝒟 h𝒟 Aop Bop C (4 * zeta) hAB hC
  have hclose' :
      |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase6FirstReverse - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase5PaperRemoved| ≤
        2 * Real.sqrt zeta := by
    calc
      |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase6FirstReverse - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase5PaperRemoved|
          = |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state (Aop q a * C q a b)) -
            _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state (Bop q a * C q a b))| := by
              rw [hreverse_norm, hpaper_norm]
      _ ≤ Real.sqrt (4 * zeta) := hclose
      _ = 2 * Real.sqrt zeta := by
            rw [Real.sqrt_mul (show 0 ≤ (4 : _root_.LIDT.MIPStarRE.LDT.Error) by positivity)]
            norm_num
  calc
    |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase5PaperRemoved - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase6FirstRemoved|
        = |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase6FirstReverse - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase5PaperRemoved| := by
          rw [← hproject, abs_sub_comm]
    _ ≤ 2 * Real.sqrt zeta := hclose'
