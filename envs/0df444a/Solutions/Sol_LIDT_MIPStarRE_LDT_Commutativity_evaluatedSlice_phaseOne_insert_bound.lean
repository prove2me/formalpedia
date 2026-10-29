-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseOne_insert_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:47:24.194455+00:00
-- url     : https://prove2.me/submissions/d76b15cf-2f1f-40ef-9682-9ee1321f550d

-- Generated proof for MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseOne_insert_bound.
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

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Commutativity/EvaluatedSliceBounds/PhaseOneThree.lean. -/
/-!
# Section 11 commutativity: the phase-1 evaluated-slice insertion bound

Closeness-of-inner-product side conditions for inserting Bob's measurement
into the first evaluated-slice step of the paper proof.  The normalization
lemmas remain formulated at the level needed by the evaluated-slice transport
arguments, but the public bound in this file is now the phase-1 insertion
estimate.

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

private lemma leftTensor_normalizationConditionSquare_le_one
    {OutcomeA OutcomeB : Type*} [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) :
    ∑ a : OutcomeA,
        (∑ b : OutcomeB,
          leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b)) *
        (∑ b : OutcomeB,
          leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ ≤
      1 := by
  let T : OutcomeA → MIPStarRE.Quantum.Op ι := fun a =>
    ∑ b : OutcomeB, Q.outcome b * P.outcome a * Q.outcome b
  calc
    ∑ a : OutcomeA,
        (∑ b : OutcomeB,
          leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b)) *
        (∑ b : OutcomeB,
          leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ
      = ∑ a : OutcomeA, leftTensor (ι₂ := ι) (T a * (T a)ᴴ) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          have hsum :
              (∑ b : OutcomeB,
                  leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b)) =
                leftTensor (ι₂ := ι) (T a) := by
            simp [T, leftTensor_finset_sum]
          rw [hsum]
          have hleft_adj :
              (leftTensor (ι₂ := ι) (T a))ᴴ = leftTensor (ι₂ := ι) ((T a)ᴴ) := by
            simpa [leftTensor, opTensor] using
              (conjTranspose_opTensor (ι₁ := ι) (ι₂ := ι)
                (T a) (1 : MIPStarRE.Quantum.Op ι))
          rw [hleft_adj, leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (∑ a : OutcomeA, T a * (T a)ᴴ) := by
          rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ (fun a => T a * (T a)ᴴ)]
    _ = leftTensor (ι₂ := ι) (normalizationConditionSquareOperator P Q) := by
          simp [T, normalizationConditionSquareOperator,
            normalizationConditionSquareFamily,
            normalizationConditionSandwichedTotalOperator,
            normalizationConditionSandwichedTotalFamily,
            normalizationConditionSandwichedFamily,
            normalizationConditionSandwichedOperator, postprocess]
    _ ≤ 1 := by
          exact leftTensor_le_one (ι₂ := ι) <| by
            simpa [normalizationConditionSquareOperator] using
              (normalizationConditionSquareFamily P Q).total_le_one





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
# Section 11 commutativity: the phase-1 evaluated-slice insertion bound

Closeness-of-inner-product side conditions for inserting Bob's measurement
into the first evaluated-slice step of the paper proof.  The normalization
lemmas remain formulated at the level needed by the evaluated-slice transport
arguments, but the public bound in this file is now the phase-1 insertion
estimate.

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
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hnorm : strategy.state.IsNormalized)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (hcombined_snd : _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
      (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft params family q.2)
      (fun q =>
        (_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy) q.2))
      (4 * zeta)) :
    let 𝒟 := _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)
    let inserted : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
      ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
                ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a)) *
            ((_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy) q.2).outcome b))
    |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
        (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
          _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab) -
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 inserted| ≤ 2 * Real.sqrt zeta := by
  let pointMeas : _root_.LIDT.MIPStarRE.LDT.IdxMeas (_root_.LIDT.MIPStarRE.LDT.Point params.next) (_root_.LIDT.MIPStarRE.LDT.Fq params) ι :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePointMeas params strategy
  let 𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params) :=
    _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)
  let A : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q => (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ι) (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q)).outcome
  let B : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b =>
      ((_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
        pointMeas q.2).outcome b)
  let C : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.Fq params →
      _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b a =>
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
        (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
          ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
          ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a))
  have h𝒟 :
      ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using
      _root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)
  have hAB :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (A q) (B q)) ≤ 4 * zeta := by
    simpa [𝒟, A, B, pointMeas, _root_.LIDT.MIPStarRE.LDT.Parameters.next, _root_.LIDT.MIPStarRE.LDT.sddError, _root_.LIDT.MIPStarRE.LDT.qSDD,
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft,
      _root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas, _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft, _root_.LIDT.MIPStarRE.LDT.SubMeas.liftLeft,
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily] using
      hcombined_snd.squaredDistanceBound
  have hC :
      ∀ q,
        ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
          (∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, C q b a) * (∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, C q b a)ᴴ ≤ 1 := by
    intro q
    simpa [C, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor,
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstProj] using
      leftTensor_normalizationConditionSquare_le_one
        (ι := ι)
        (P := _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q)
        (Q := _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstProj params family q)
  have hzeta_nonneg : 0 ≤ zeta := by
    have hsdd_nonneg :
        0 ≤ _root_.LIDT.MIPStarRE.LDT.sddError strategy.state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)) q.2)
          (fun q =>
            (_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
              pointMeas q.2)) := by
      exact _root_.LIDT.MIPStarRE.LDT.sddError_nonneg strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (fun q => (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)) q.2)
        (fun q =>
          (_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily params family)
            pointMeas q.2))
    have hfour : 0 ≤ 4 * zeta := le_trans hsdd_nonneg hcombined_snd.squaredDistanceBound
    nlinarith
  have hABAB :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
          (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab) =
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
          (fun q => ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (C q b a * A q b)) := by
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro q
    calc
      ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab
        = ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                  ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
                  ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                  ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b))) := by
              simpa [_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor,
                _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor,
                mul_assoc] using
                (Fintype.sum_prod_type' (f := fun a : _root_.LIDT.MIPStarRE.LDT.Fq params => fun b : _root_.LIDT.MIPStarRE.LDT.Fq params =>
                  _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                        ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
                        ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                        ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b)))))
      _ = ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C q b a * A q b) := by
              rw [Finset.sum_comm]
              simp [A, C, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor, mul_assoc]
  have hclose :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C (4 * zeta) hAB hC
  calc
    |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
        (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
          _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab) -
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
        (fun q => ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
          _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C q b a * B q b))| =
        |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C q b a * A q b)) -
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C q b a * B q b))| := by
          rw [hABAB]
    _ ≤ Real.sqrt (4 * zeta) := hclose
    _ = 2 * Real.sqrt zeta := by
          rw [Real.sqrt_mul (show 0 ≤ (4 : _root_.LIDT.MIPStarRE.LDT.Error) by positivity)]
          norm_num
