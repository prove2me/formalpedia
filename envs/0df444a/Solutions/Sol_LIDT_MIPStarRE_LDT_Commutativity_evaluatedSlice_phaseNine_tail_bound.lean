-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseNine_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:54:09.746746+00:00
-- url     : https://prove2.me/submissions/a44ccb37-91b3-4df3-909c-d277ea3f2b4a

-- Generated proof for MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseNine_tail_bound.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_leftTensor_pair_prefix_adjoint_normalization

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
# Tail endpoints for the evaluated-slice paper chain

This file proves the two postprocessed self-consistency tail moves at the
end of the paper-faithful scalar chain.
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
    (hpostSSC_snd : _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
      (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft params family q.2)
      (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyRight params family q.2)
      zeta) :
    let 𝒟 := _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)
    let phase8TailRight : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error :=
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseEightTailRight params strategy family
    let avgBAB : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
      ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
        _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABTerm params strategy family q ab
    |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase8TailRight - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgBAB| ≤ Real.sqrt zeta := by
  let 𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params) :=
    _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)
  let phase8TailRight : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseEightTailRight params strategy family
  let avgBAB : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABTerm params strategy family q ab
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using
      _root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params)
  let Aop : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b => _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b)
  let Bop : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b => _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b)
  let C : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.Fq params →
      _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := fun q b a =>
    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
      (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
        ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b))
  have hAop_herm : ∀ q b, (Aop q b)ᴴ = Aop q b := by
    intro q b
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (_root_.LIDT.MIPStarRE.LDT.leftTensor_nonneg (ι₂ := ι)
          ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome_pos b))).isHermitian.eq
  have hBop_herm : ∀ q b, (Bop q b)ᴴ = Bop q b := by
    intro q b
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (_root_.LIDT.MIPStarRE.LDT.rightTensor_nonneg (ι₁ := ι)
          ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome_pos b))).isHermitian.eq
  have hAB :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q =>
        _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (fun b => (Aop q b)ᴴ) (fun b => (Bop q b)ᴴ)) ≤
        zeta := by
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q =>
          _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (fun b => (Aop q b)ᴴ) (fun b => (Bop q b)ᴴ))
          = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (Aop q) (Bop q)) := by
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            intro q
            simp only [_root_.LIDT.MIPStarRE.LDT.qSDDCore, hAop_herm q, hBop_herm q]
      _ ≤ zeta := by
          have hbound := hpostSSC_snd.squaredDistanceBound
          change _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (Aop q) (Bop q)) ≤
            zeta at hbound
          exact hbound
  have hC :
      ∀ q,
        ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, (∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, C q b a)ᴴ * (∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, C q b a) ≤ 1 := by
    intro q
    simpa [C] using
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.leftTensor_pair_prefix_adjoint_normalization
        (A := _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q)
        (B := _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q))
  have htail_norm :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase8TailRight =
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
          _root_.LIDT.MIPStarRE.LDT.ev strategy.state (Bop q b * C q b a)) := by
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro q
    dsimp [phase8TailRight, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseEightTailRight, Bop, C]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro a _
    congr 1
    simp [_root_.LIDT.MIPStarRE.LDT.opTensor_mul]
  have hbab_norm :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgBAB =
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
          _root_.LIDT.MIPStarRE.LDT.ev strategy.state (Aop q b * C q b a)) := by
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro q
    dsimp [avgBAB, Aop, C]
    calc
      ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABTerm params strategy family q ab
          = ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                  (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
                    ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                    ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b))) := by
            simpa [_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABTerm, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor]
              using (Fintype.sum_prod_type' (f := fun a : _root_.LIDT.MIPStarRE.LDT.Fq params => fun b : _root_.LIDT.MIPStarRE.LDT.Fq params =>
                _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    (((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b) *
                      ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceFirstFactor params family q).outcome a) *
                      ((_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceSecondFactor params family q).outcome b)))))
      _ = ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (Aop q b * C q b a) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro b _
            refine Finset.sum_congr rfl ?_
            intro a _
            congr 1
            rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor, mul_assoc]
  have hclose :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.closenessOfIPAdjoint
      strategy.state hnorm 𝒟 h𝒟 Aop Bop C zeta hAB hC
  calc
    |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 phase8TailRight - _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 avgBAB|
        = |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (Bop q b * C q b a)) -
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (Aop q b * C q b a))| := by
            rw [htail_norm, hbab_norm]
    _ = |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (Aop q b * C q b a)) -
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ b : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (Bop q b * C q b a))| := by
            rw [abs_sub_comm]
    _ ≤ Real.sqrt zeta := hclose
