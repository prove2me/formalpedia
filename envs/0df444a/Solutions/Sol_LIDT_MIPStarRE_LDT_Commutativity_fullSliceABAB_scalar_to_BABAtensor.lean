-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAB_scalar_to_BABAtensor
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:05:52.364089+00:00
-- url     : https://prove2.me/submissions/1ea9384d-fdad-4b4e-83ea-809621b56b35

-- Generated proof for MIPStarRE.LDT.Commutativity.fullSliceABAB_scalar_to_BABAtensor.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_fullSliceCommutation_avg_swap_terms
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_fullSlice_selfConsistency_fst_bound
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
# Core full-slice closeness-of-inner-product comparison

Standalone `closenessOfIP` scalar↔tensor comparison lemma extracted from
`Closeness.lean` per #1127.  This lemma is the core
tensor-form machinery that moves a trailing measurement outcome between
the scalar quartic and a manifestly positive tensor register.

The tensor-form lemmas are internal to the scalar/tensor comparison recorded in
`docs/decisions/713-scalar-tensor-decision.md`; downstream code should use
the scalar public API exposed by
`Closeness.lean` and `ClosenessXEval.lean`.

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
    |_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family -
        _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABAtensorAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params) :=
    _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params)
  let A : _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Polynomial params → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun xy g => _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((family.meas xy.1).toSubMeas.outcome g)
  let B : _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Polynomial params → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun xy g => _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((family.meas xy.1).toSubMeas.outcome g)
  let C : _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Polynomial params → _root_.LIDT.MIPStarRE.LDT.Polynomial params →
      _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun xy g h =>
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
        ((family.meas xy.2).toSubMeas.outcome h *
          (family.meas xy.1).toSubMeas.outcome g *
          (family.meas xy.2).toSubMeas.outcome h)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using _root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params)
  have hAB : _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun xy => _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (A xy) (B xy)) ≤ zeta := by
    simpa [𝒟, A, B] using _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSlice_selfConsistency_fst_bound params strategy family zeta hself
  have hC :
      ∀ xy,
        ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            (∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params, C xy g h) * (∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params, C xy g h)ᴴ ≤
          1 := by
    intro xy
    simpa [C, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceFirstFactor, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceSecondProj] using
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.leftTensor_normalizationCondition_sandwich_bound
        (P := _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceFirstFactor params family xy)
        (Q := _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceSecondProj params family xy))
  have hclose :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hBABA_to_ABAB := (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceCommutation_avg_swap_terms params strategy family).2
  have hScalar :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
          (fun xy => ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C xy g h * A xy g)) =
        _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family := by
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
          (fun xy => ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C xy g h * A xy g))
        = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
            (fun xy => ∑ gh : _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceOutcome params,
              _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABATerm params strategy family xy gh) := by
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            intro xy
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro g _
            refine Finset.sum_congr rfl ?_
            intro h _
            simp [C, A, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABATerm, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceFirstFactor, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceSecondFactor,
              _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor, mul_assoc]
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
            (fun xy => ∑ gh : _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceOutcome params,
              _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABTerm params strategy family xy gh) := by
            simpa [𝒟] using hBABA_to_ABAB
      _ = _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family := by
            rfl
  have hTensor :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
          (fun xy => ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C xy g h * B xy g)) =
        _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABAtensorAvg params strategy family := by
    unfold _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABAtensorAvg
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro xy
    simpa [C, B] using
      (Fintype.sum_prod_type' (f := fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => fun h : _root_.LIDT.MIPStarRE.LDT.Polynomial params =>
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((family.meas xy.2).toSubMeas.outcome h *
                (family.meas xy.1).toSubMeas.outcome g *
                (family.meas xy.2).toSubMeas.outcome h) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι)
              ((family.meas xy.1).toSubMeas.outcome g)))).symm
  calc
    |_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family - _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABAtensorAvg params strategy family|
      = |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
            (fun xy => ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C xy g h * A xy g)) -
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
            (fun xy => ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state (C xy g h * B xy g))| := by
            rw [hScalar, hTensor]
    _ ≤ Real.sqrt zeta := hclose
