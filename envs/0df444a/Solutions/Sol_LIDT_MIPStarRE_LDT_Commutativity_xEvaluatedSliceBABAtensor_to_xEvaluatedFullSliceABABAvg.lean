-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedSliceBABAtensor_to_xEvaluatedFullSliceABABAvg
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:08:57.954727+00:00
-- url     : https://prove2.me/submissions/9865f29b-f0d6-4efa-acce-e55965a15278

-- Generated proof for MIPStarRE.LDT.Commutativity.xEvaluatedSliceBABAtensor_to_xEvaluatedFullSliceABABAvg.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_leftTensor_normalizationCondition_sandwich_adjoint_bound
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_xEvaluatedSliceBABAtensorAvg_eq_xFullData
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_xEvaluated_selfConsistency_fst_bound

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Commutativity/Transport/FullSlice/Bridges/Closeness.lean. -/
/-!
# Full-slice scalar-to-tensor closeness comparison

`closenessOfIP` comparisons transform scalar quartic averages into manifestly
positive tensor-form partners.  The same route includes tensor-marginalization
identities connecting full-slice and evaluated-slice `ABAB` averages.

The core `closenessOfIP` scalar↔tensor comparison lemmas are factored into
`ClosenessCore.lean` (extracted per #1127).

The tensor-form lemmas are internal to the scalar/tensor comparison recorded in
`docs/decisions/713-scalar-tensor-decision.md`; downstream code should use the
scalar public API exposed by the full-slice transport theorems.

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

private lemma leftTensor_sandwich_adjoint_normalization_family
    {Ω α β : Type*} [Fintype α] [Fintype β]
    (P : Ω → SubMeas α ι) (Q : Ω → ProjSubMeas β ι) :
    ∀ ω,
      ∑ a : α,
          (∑ b : β,
            leftTensor (ι₂ := ι) ((Q ω).outcome b * (P ω).outcome a * (Q ω).outcome b))ᴴ *
            (∑ b : β,
              leftTensor (ι₂ := ι) ((Q ω).outcome b * (P ω).outcome a * (Q ω).outcome b)) ≤
        1 := by
  intro ω
  simpa using
    leftTensor_normalizationCondition_sandwich_adjoint_bound
      (ι := ι) (P := P ω) (Q := Q ω)










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
# Full-slice scalar-to-tensor closeness comparison

`closenessOfIP` comparisons transform scalar quartic averages into manifestly
positive tensor-form partners.  The same route includes tensor-marginalization
identities connecting full-slice and evaluated-slice `ABAB` averages.

The core `closenessOfIP` scalar↔tensor comparison lemmas are factored into
`ClosenessCore.lean` (extracted per #1127).

The tensor-form lemmas are internal to the scalar/tensor comparison recorded in
`docs/decisions/713-scalar-tensor-decision.md`; downstream code should use the
scalar public API exposed by the full-slice transport theorems.

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
    |_root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedSliceBABAtensorAvg params strategy family -
        _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params) :=
    _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params)
  let X : _root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) ι :=
    fun ux => _root_.LIDT.MIPStarRE.LDT.evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
  let Y : _root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ι :=
    fun ux => (family.meas ux.2.2).toSubMeas
  let A : _root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Fq params →
      _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux a => _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((X ux).outcome a)
  let B : _root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Fq params →
      _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux a => _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((X ux).outcome a)
  let C : _root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params → _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.Polynomial params →
      _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux a h => _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
      ((Y ux).outcome h * (X ux).outcome a * (Y ux).outcome h)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using _root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one
      (_root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params)
  have hAB :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
        (fun ux => _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (fun a => (A ux a)ᴴ) (fun a => (B ux a)ᴴ)) ≤
        zeta := by
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
          (fun ux => _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (fun a => (A ux a)ᴴ) (fun a => (B ux a)ᴴ))
        = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun ux => _root_.LIDT.MIPStarRE.LDT.qSDDCore strategy.state (A ux) (B ux)) := by
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            intro ux
            unfold _root_.LIDT.MIPStarRE.LDT.qSDDCore
            apply Finset.sum_congr rfl
            intro a _
            have hX : ((X ux).outcome a)ᴴ = (X ux).outcome a := (X ux).outcome_hermitian a
            simp [A, B, hX]
      _ ≤ zeta := by
            simpa [𝒟, A, B, X] using
              _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluated_selfConsistency_fst_bound params strategy family zeta hself
  have hC :
      ∀ ux,
        ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params,
            (∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params, C ux a h)ᴴ *
              (∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params, C ux a h) ≤ 1 := by
    intro ux
    simpa [C, X, Y] using
      leftTensor_sandwich_adjoint_normalization_family
        (ι := ι) (P := X) (Q := fun ux => family.meas ux.2.2) ux
  have hclose :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.closenessOfIPAdjoint
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hScalar :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun ux => ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state (A ux a * C ux a h)) =
        _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABAvg params strategy family := by
    unfold _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABAvg
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro ux
    calc
      ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
          _root_.LIDT.MIPStarRE.LDT.ev strategy.state (A ux a * C ux a h)
        = ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((X ux).outcome a * (Y ux).outcome h * (X ux).outcome a *
                  (Y ux).outcome h)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro h _
            simp [A, C, X, Y, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor, mul_assoc]
      _ = ∑ ah : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((X ux).outcome ah.1 * (Y ux).outcome ah.2 * (X ux).outcome ah.1 *
                  (Y ux).outcome ah.2)) := by
            exact (Fintype.sum_prod_type' (f := fun a : _root_.LIDT.MIPStarRE.LDT.Fq params =>
              fun h : _root_.LIDT.MIPStarRE.LDT.Polynomial params =>
                _root_.LIDT.MIPStarRE.LDT.ev strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    ((X ux).outcome a * (Y ux).outcome h * (X ux).outcome a *
                      (Y ux).outcome h)))).symm
  have hTensor :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun ux => ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state (B ux a * C ux a h)) =
        _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedSliceBABAtensorAvg params strategy family := by
    rw [_root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedSliceBABAtensorAvg_eq_xFullData params strategy family]
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro ux
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro h _
    rw [_root_.LIDT.MIPStarRE.LDT.rightTensor_mul_leftTensor_eq_opTensor,
      ← _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
  calc
    |_root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedSliceBABAtensorAvg params strategy family -
        _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABAvg params strategy family|
      = |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun ux => ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (B ux a * C ux a h)) -
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun ux => ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (A ux a * C ux a h))| := by
          rw [hTensor, hScalar]
    _ = |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun ux => ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (A ux a * C ux a h)) -
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun ux => ∑ a : _root_.LIDT.MIPStarRE.LDT.Fq params, ∑ h : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
            _root_.LIDT.MIPStarRE.LDT.ev strategy.state (B ux a * C ux a h))| := by
          rw [abs_sub_comm]
    _ ≤ Real.sqrt zeta := hclose
