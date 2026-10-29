-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseFour_pointSwap_right_bound_of_commutativityPoints
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:19:23.210768+00:00
-- url     : https://prove2.me/submissions/37d0fa20-19e7-46b0-a556-8a64ef599f54

-- Generated proof for MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseFour_pointSwap_right_bound_of_commutativityPoints.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_qSDDOp_symm

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/CommutativityPoints/SharedHelpers/Core.lean. -/
/-!
# Section 10 commutativity points: shared helpers core

Shared reindexing and tensor-placement helpers used by the Section 10
commutativity-of-points argument.

## References

- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators
/-! ## Shared reindexing and tensor-placement helpers -/

lemma sddOpRel_symm
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ : Error) :
    SDDOpRel ψ 𝒟 A B δ →
      SDDOpRel ψ 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  simpa [sddErrorOp, MIPStarRE.LDT.Preliminaries.qSDDOp_symm] using h

















end MIPStarRE.LDT.CommutativityPoints

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







/-- `prop:closeness-of-ip` (`eq:closeness3`).

If `A ≈_γ B` (raw matrices) and `Σ_a (Σ_b C_{a,b})(Σ_b C_{a,b})† ≤ I`,
then
`|𝔼_x Σ_{a,b} ⟨ψ| C_{a,b} A_a |ψ⟩ -
  𝔼_x Σ_{a,b} ⟨ψ| C_{a,b} B_a |ψ⟩| ≤ √γ`. -/
theorem closenessOfIP
    {Question OutcomeA OutcomeB : Type*} {ι : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (γ : Error)
    (hAB : avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q)) ≤ γ)
    (hC :
      ∀ q,
        ∑ a : OutcomeA,
          (∑ b : OutcomeB, C q a b) * (∑ b : OutcomeB, C q a b)ᴴ ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a))| ≤
      Real.sqrt γ := by
  simpa using closenessOfInnerProduct_left ψ hψ 𝒟 h𝒟 A B C γ hAB hC





end MIPStarRE.LDT.Preliminaries

end

end LIDT

open LIDT
/-!
# Point-swap bound for the evaluated-slice paper chain

This file contains the right-register point-swap estimate used in the
paper-faithful scalar chain for `lem:comm-data-processed-g`.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (gamma : _root_.LIDT.MIPStarRE.LDT.Error)
    (hnorm : strategy.state.IsNormalized)
    (hcomm :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.GlobalVariance.PointPairQuestion params.next))
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductLeft params.next strategy)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductRight params.next strategy)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError params.next gamma))
    (C : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params →
      _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι))
    (hC : ∀ q, ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params, C q ab * (C q ab)ᴴ ≤ 1) :
    let 𝒟 := _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)
    let inserted : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
      ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
          (C q ab *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
               ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))
    let swapped : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
      ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
          (C q ab *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
               ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome ab.2)))
    |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 inserted - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 swapped| ≤
      6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) := by
  let 𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params) :=
    _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)
  let Rrev : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params →
      _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q ab => _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
      (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
        ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome ab.1))
  let Rord : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params →
      _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q ab => _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
      (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
        ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).outcome ab.2))
  let C' : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params → Unit →
      _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun q ab _ => C q ab
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using _root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)
  let Lrev : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.OpFamily (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params) (ι × ι) :=
    fun q => _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily (ιB := ι) <|
      _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.reversedProductOpFamily
        ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).toSubMeas : _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) ι)
        ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).toSubMeas : _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) ι)
  let Lord : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.OpFamily (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params) (ι × ι) :=
    fun q => _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily (ιB := ι) <|
      _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.orderedProductOpFamily
        ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).toSubMeas : _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) ι)
        ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).toSubMeas : _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) ι)
  have hleft :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state 𝒟 Lord Lrev (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError params.next gamma) := by
    change
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.GlobalVariance.PointPairQuestion params.next))
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductLeft params.next strategy)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductRight params.next strategy)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError params.next gamma)
    exact hcomm
  have hleft_symm :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state 𝒟 Lrev Lord (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError params.next gamma) := by
    exact _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_symm strategy.state 𝒟 Lord Lrev
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError params.next gamma) hleft
  have hAB : _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (Rrev q) (Rord q)) ≤
      _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError params.next gamma := by
    rcases hleft_symm with ⟨h⟩
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (Rrev q) (Rord q))
          = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDOp strategy.state (Lrev q) (Lord q)) := by
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            intro q
            simpa [_root_.LIDT.MIPStarRE.LDT.qSDDOp, Lrev, Lord, Rrev, Rord, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas,
              _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily, _root_.LIDT.MIPStarRE.LDT.OpFamily.rightPlacedOpFamily,
              _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.reversedProductOpFamily, _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.orderedProductOpFamily, _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.PointPairOutcome,
              _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome, _root_.LIDT.MIPStarRE.LDT.Parameters.next] using
              (_root_.LIDT.MIPStarRE.LDT.Preliminaries.qSDDCore_rightTensor_eq_leftTensor_of_permInv
                (ι := ι) (ψ := strategy.state) strategy.permInvState
                (fun ab =>
                  (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.reversedProductOpFamily
                    ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).toSubMeas :
                      _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) ι)
                    ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).toSubMeas :
                      _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) ι)).outcome ab)
                (fun ab =>
                  (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.orderedProductOpFamily
                    ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.1).toSubMeas :
                      _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) ι)
                    ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy q.2).toSubMeas :
                      _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) ι)).outcome ab))
      _ ≤ _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError params.next gamma := by
            simpa [_root_.LIDT.MIPStarRE.LDT.sddErrorOp] using h
  have hC' :
      ∀ q,
        ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            (∑ _ : Unit, C' q ab ()) * (∑ _ : Unit, C' q ab ())ᴴ ≤ 1 := by
    intro q
    simpa [C'] using hC q
  have hclose :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 Rrev Rord C' (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError params.next gamma) hAB hC'
  have hsqrt32_le_six : Real.sqrt (32 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 6 := by
    have hsqrt32_nonneg : 0 ≤ Real.sqrt (32 : _root_.LIDT.MIPStarRE.LDT.Error) := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt (show 0 ≤ (32 : _root_.LIDT.MIPStarRE.LDT.Error) by positivity)]
  calc
    |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
        (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
          _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C q ab * Rrev q ab)) -
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
        (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
          _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C q ab * Rord q ab))|
      ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError params.next gamma) := by
          simpa [𝒟, Rrev, Rord, C'] using hclose
    _ = Real.sqrt (32 : _root_.LIDT.MIPStarRE.LDT.Error) * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) := by
          rw [_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError, _root_.LIDT.MIPStarRE.LDT.Parameters.next]
          have hring :
              32 * gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error) =
                (32 : _root_.LIDT.MIPStarRE.LDT.Error) * (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            ring
          rw [hring, Real.sqrt_mul (show 0 ≤ (32 : _root_.LIDT.MIPStarRE.LDT.Error) by positivity)]
    _ ≤ 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : _root_.LIDT.MIPStarRE.LDT.Error)) := by
          exact mul_le_mul_of_nonneg_right hsqrt32_le_six (Real.sqrt_nonneg _)
