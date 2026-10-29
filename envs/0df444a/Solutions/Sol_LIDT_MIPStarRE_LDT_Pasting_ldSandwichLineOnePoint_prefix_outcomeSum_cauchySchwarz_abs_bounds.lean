-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_abs_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:29:11.74243+00:00
-- url     : https://prove2.me/submissions/e279a314-7607-46a3-a046-ee6de0dc7473

-- Generated proof for MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_abs_bounds.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_BackChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Chain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_FlatChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_PrefixMoved
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Core_LdGbcon
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_ScalarTerms
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_facts

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
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
# Section 12 pasting: line one-point transport — Cauchy-Schwarz chain

Internal helper module; part of the file-split for `#1127`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (facts : _root_.LIDT.MIPStarRE.LDT.Pasting.LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.LdSandwichLineOnePointOutcomeSumCSAbsBounds params strategy family gamma zeta hi := by
  let 𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k) :=
    _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using _root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k)
  have csFacts :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_facts
      params strategy family gamma zeta hi hi0 facts
  refine ⟨?_, ?_⟩
  · have hfirst :=
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.closenessOfIPAdjoint
        strategy.state strategy.isNormalized 𝒟 h𝒟
        (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Aord params family hi)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Arot params family hi)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Cfirst params strategy family hi)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta (i + 1))
        (by simpa [𝒟] using csFacts.adjointRawCore)
        csFacts.firstUnitBound
    rw [csFacts.source_eq_firstSourceRaw, csFacts.afterFirst_eq_firstTargetRaw]
    simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_firstSourceRaw,
      _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_firstTargetRaw, 𝒟] using hfirst
  · have hsecond :=
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.closenessOfIP
        strategy.state strategy.isNormalized 𝒟 h𝒟
        (fun (q : _root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k)
            (gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1)) =>
          (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ)
        (fun (q : _root_.LIDT.MIPStarRE.LDT.Pasting.SandwichedLineQuestion params k)
            (gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params (i + 1)) =>
          (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Csecond params strategy family hi)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.commuteGHalfSandwichError params gamma zeta (i + 1))
        (by simpa [𝒟] using csFacts.adjointRawCore)
        csFacts.secondUnitBound
    rw [csFacts.afterFirst_eq_secondSourceRaw, csFacts.moved_eq_secondTargetRaw]
    simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_secondSourceRaw,
      _root_.LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_secondTargetRaw, 𝒟] using hsecond
