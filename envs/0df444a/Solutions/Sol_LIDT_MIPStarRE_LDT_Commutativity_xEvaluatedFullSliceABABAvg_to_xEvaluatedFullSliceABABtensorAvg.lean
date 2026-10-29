-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABAvg_to_xEvaluatedFullSliceABABtensorAvg
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:05:52.232334+00:00
-- url     : https://prove2.me/submissions/64aa7f26-d8bf-4e49-b274-1035762addaf

-- Generated proof for MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABAvg_to_xEvaluatedFullSliceABABtensorAvg.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_fullSlice_selfConsistency_snd_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_leftTensor_normalizationCondition_sandwich_bound

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
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
# X-evaluated full-slice closeness comparison

Single `closenessOfIP` comparison for the x-evaluated/full-y scalar-to-tensor
transition; extracted from `Closeness.lean` per #1127.

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
    |_root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABAvg params strategy family -
        _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABtensorAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params) :=
    _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params)
  let A : _root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Polynomial params →
      _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux h => _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((family.meas ux.2.2).toSubMeas.outcome h)
  let B : _root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Polynomial params →
      _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux h => _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((family.meas ux.2.2).toSubMeas.outcome h)
  let C : _root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Polynomial params → _root_.LIDT.MIPStarRE.LDT.Fq params →
      _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux h a =>
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
        ((_root_.LIDT.MIPStarRE.LDT.evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a *
          (family.meas ux.2.2).toSubMeas.outcome h *
          (_root_.LIDT.MIPStarRE.LDT.evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using _root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one
      (_root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params)
  have hAB : _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun ux => _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (A ux) (B ux)) ≤ zeta := by
    have hsnd :=
      _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_snd (α := _root_.LIDT.MIPStarRE.LDT.Point params) (β := _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params)
        (f := fun xy =>
          _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state
            (fun h : _root_.LIDT.MIPStarRE.LDT.Polynomial params =>
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((family.meas xy.2).toSubMeas.outcome h))
            (fun h : _root_.LIDT.MIPStarRE.LDT.Polynomial params =>
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)))
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun ux => _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (A ux) (B ux))
        = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params))
            (fun xy =>
              _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state
                (fun h : _root_.LIDT.MIPStarRE.LDT.Polynomial params =>
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((family.meas xy.2).toSubMeas.outcome h))
                (fun h : _root_.LIDT.MIPStarRE.LDT.Polynomial params =>
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h))) := by
            simpa [𝒟, A, B] using hsnd
      _ ≤ zeta := _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSlice_selfConsistency_snd_bound params strategy family zeta hself
  have hC :
      ∀ ux,
        ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            (∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, C ux h a) * (∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, C ux h a)ᴴ ≤ 1 := by
    intro ux
    let P : _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ι := _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceSecondFactor params family ux.2
    let Q : _root_.LIDT.MIPStarRE.LDT.ProjSubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) ι :=
      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluateAtProjSubMeas params ux.1 (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceFirstProj params family ux.2)
    simpa [C, P, Q, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluateAtProjSubMeas, _root_.LIDT.MIPStarRE.LDT.evaluateAt, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceFirstProj,
      _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceSecondFactor] using
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.leftTensor_normalizationCondition_sandwich_bound (P := P) (Q := Q))
  have hclose :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hScalar :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
          (fun ux => ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C ux h a * A ux h)) =
        _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABAvg params strategy family := by
    unfold _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABAvg
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    rintro ⟨u, xy⟩
    calc
      ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
          _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C (u, xy) h a * A (u, xy) h)
        = ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((_root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                  (family.meas xy.2).toSubMeas.outcome h *
                  (_root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                  (family.meas xy.2).toSubMeas.outcome h)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro h _
            simp [C, A, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor, mul_assoc]
      _ = ∑ ah : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((_root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome ah.1 *
                  (family.meas xy.2).toSubMeas.outcome ah.2 *
                  (_root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome ah.1 *
                  (family.meas xy.2).toSubMeas.outcome ah.2)) := by
            exact (Fintype.sum_prod_type' (f := fun a : _root_.LIDT.MIPStarRE.LDT.Fq params =>
              fun h : _root_.LIDT.MIPStarRE.LDT.Polynomial params =>
                _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    ((_root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                      (family.meas xy.2).toSubMeas.outcome h *
                      (_root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                      (family.meas xy.2).toSubMeas.outcome h)))).symm
  have hTensor :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
          (fun ux => ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C ux h a * B ux h)) =
        _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABtensorAvg params strategy family := by
    unfold _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABtensorAvg
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    rintro ⟨u, xy⟩
    calc
      ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
          _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C (u, xy) h a * B (u, xy) h)
        = ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                  ((_root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                    (family.meas xy.2).toSubMeas.outcome h *
                    (_root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)) := by
            rw [Finset.sum_comm]
      _ = ∑ ah : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                  ((_root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome ah.1 *
                    (family.meas xy.2).toSubMeas.outcome ah.2 *
                    (_root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome ah.1) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome ah.2)) := by
            exact (Fintype.sum_prod_type' (f := fun a : _root_.LIDT.MIPStarRE.LDT.Fq params =>
              fun h : _root_.LIDT.MIPStarRE.LDT.Polynomial params =>
                _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      ((_root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                        (family.meas xy.2).toSubMeas.outcome h *
                        (_root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a) *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)))).symm
  calc
    |_root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABAvg params strategy family -
        _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABtensorAvg params strategy family|
      = |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
            (fun ux => ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C ux h a * A ux h)) -
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
            (fun ux => ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C ux h a * B ux h))| := by
            rw [hScalar, hTensor]
    _ ≤ Real.sqrt zeta := hclose
