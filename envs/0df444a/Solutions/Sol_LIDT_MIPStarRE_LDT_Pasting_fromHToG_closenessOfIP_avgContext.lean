-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToG_closenessOfIP_avgContext
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:43:57.331057+00:00
-- url     : https://prove2.me/submissions/a370aa60-35b6-4b59-a17b-ce9ec8a77483

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToG_closenessOfIP_avgContext.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_BernoulliTail
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_FactBundles
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
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
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic

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

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/MoveLemmas/Basic.lean. -/
/-!
# Section 12 pasting: from-H-to-G move lemmas

Tensor, positivity, and Cauchy--Schwarz helper lemmas for the adjacent paper chain.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

































lemma fromHToG_avgOver_sub {Question : Type*}
    (𝒟 : Distribution Question) (f g : Question → Error) :
    avgOver 𝒟 f - avgOver 𝒟 g = avgOver 𝒟 (fun q => f q - g q) := by
  unfold avgOver
  calc
    ∑ q ∈ 𝒟.support, 𝒟.weight q * f q - ∑ q ∈ 𝒟.support, 𝒟.weight q * g q
      = ∑ q ∈ 𝒟.support, (𝒟.weight q * f q - 𝒟.weight q * g q) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ q ∈ 𝒟.support, 𝒟.weight q * (f q - g q) := by
          refine Finset.sum_congr rfl ?_
          intro q _hq
          ring









end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: from-H-to-G move lemmas

Tensor, positivity, and Cauchy--Schwarz helper lemmas for the adjacent paper chain.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    {Question OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι)) (_hψ : ψ.IsNormalized)
    (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (_h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι))
    (C : Question → OutcomeA → OutcomeB → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι))
    (γ : _root_.LIDT.MIPStarRE.LDT.Error)
    (hAB : _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDCore ψ (A q) (B q)) ≤ γ)
    (hC : _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q =>
      ∑ a : OutcomeA, _root_.LIDT.MIPStarRE.LDT.ev ψ ((∑ b : OutcomeB, C q a b) * (∑ b : OutcomeB, C q a b)ᴴ)) ≤ 1) :
    |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, _root_.LIDT.MIPStarRE.LDT.ev ψ (C q a b * A q a)) -
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, _root_.LIDT.MIPStarRE.LDT.ev ψ (C q a b * B q a))| ≤
      Real.sqrt γ := by
  let Csum : Question → OutcomeA → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a => ∑ b : OutcomeB, C q a b
  let D : Question → OutcomeA → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a => A q a - B q a
  let t : Question → OutcomeA → _root_.LIDT.MIPStarRE.LDT.Error := fun q a => _root_.LIDT.MIPStarRE.LDT.ev ψ (Csum q a * D q a)
  let x : Question → OutcomeA → _root_.LIDT.MIPStarRE.LDT.Error := fun q a => _root_.LIDT.MIPStarRE.LDT.ev ψ (Csum q a * (Csum q a)ᴴ)
  let y : Question → OutcomeA → _root_.LIDT.MIPStarRE.LDT.Error := fun q a => _root_.LIDT.MIPStarRE.LDT.ev ψ ((D q a)ᴴ * D q a)
  have ht : ∀ q a, |t q a| ≤ Real.sqrt (x q a) * Real.sqrt (y q a) := by
    intro q a
    exact _root_.LIDT.MIPStarRE.LDT.ev_abs_mul_le_sqrt ψ (Csum q a) (D q a)
  have hx : ∀ q a, 0 ≤ x q a := by
    intro q a
    simpa [x] using _root_.LIDT.MIPStarRE.LDT.ev_adjoint_self_nonneg ψ ((Csum q a)ᴴ)
  have hy : ∀ q a, 0 ≤ y q a := by
    intro q a
    exact _root_.LIDT.MIPStarRE.LDT.ev_adjoint_self_nonneg ψ (D q a)
  have hweighted := _root_.LIDT.MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz 𝒟 t x y ht hx hy
  have hgap :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : OutcomeA, t q a) =
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, _root_.LIDT.MIPStarRE.LDT.ev ψ (C q a b * A q a)) -
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, _root_.LIDT.MIPStarRE.LDT.ev ψ (C q a b * B q a)) := by
    have hgap_q : ∀ q,
        ∑ a : OutcomeA, t q a =
          (∑ a : OutcomeA, ∑ b : OutcomeB, _root_.LIDT.MIPStarRE.LDT.ev ψ (C q a b * A q a)) -
            ∑ a : OutcomeA, ∑ b : OutcomeB, _root_.LIDT.MIPStarRE.LDT.ev ψ (C q a b * B q a) := by
      intro q
      have hleft :
          ∑ a : OutcomeA, ∑ b : OutcomeB, _root_.LIDT.MIPStarRE.LDT.ev ψ (C q a b * A q a) =
            ∑ a : OutcomeA, _root_.LIDT.MIPStarRE.LDT.ev ψ (Csum q a * A q a) := by
        refine Finset.sum_congr rfl ?_
        intro a _ha
        dsimp [Csum]
        rw [← _root_.LIDT.MIPStarRE.LDT.ev_sum ψ (fun b : OutcomeB => C q a b * A q a), Finset.sum_mul]
      have hright :
          ∑ a : OutcomeA, ∑ b : OutcomeB, _root_.LIDT.MIPStarRE.LDT.ev ψ (C q a b * B q a) =
            ∑ a : OutcomeA, _root_.LIDT.MIPStarRE.LDT.ev ψ (Csum q a * B q a) := by
        refine Finset.sum_congr rfl ?_
        intro a _ha
        dsimp [Csum]
        rw [← _root_.LIDT.MIPStarRE.LDT.ev_sum ψ (fun b : OutcomeB => C q a b * B q a), Finset.sum_mul]
      rw [hleft, hright, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro a _ha
      dsimp [t, D]
      rw [(_root_.LIDT.MIPStarRE.LDT.ev_sub ψ (_ * _) (_ * _)).symm]
      simp [mul_sub]
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : OutcomeA, t q a)
        = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q =>
            (∑ a : OutcomeA, ∑ b : OutcomeB, _root_.LIDT.MIPStarRE.LDT.ev ψ (C q a b * A q a)) -
              ∑ a : OutcomeA, ∑ b : OutcomeB, _root_.LIDT.MIPStarRE.LDT.ev ψ (C q a b * B q a)) := by
                refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
                intro q
                exact hgap_q q
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, _root_.LIDT.MIPStarRE.LDT.ev ψ (C q a b * A q a)) -
            _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, _root_.LIDT.MIPStarRE.LDT.ev ψ (C q a b * B q a)) := by
                symm
                exact _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_avgOver_sub 𝒟 _ _
  have hy_eq :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : OutcomeA, y q a) =
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDCore ψ (A q) (B q)) := by
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
    intro q
    simp [y, D, _root_.LIDT.MIPStarRE.LDT.qSDDCore]
  have hx_nonneg : 0 ≤ _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : OutcomeA, x q a) := by
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg 𝒟 _ ?_
    intro q
    exact Finset.sum_nonneg (fun a _ha => hx q a)
  calc
    |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, _root_.LIDT.MIPStarRE.LDT.ev ψ (C q a b * A q a)) -
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, _root_.LIDT.MIPStarRE.LDT.ev ψ (C q a b * B q a))|
      = |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : OutcomeA, t q a)| := by
          rw [hgap]
    _ ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : OutcomeA, x q a)) *
          Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : OutcomeA, y q a)) := hweighted
    _ ≤ 1 * Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : OutcomeA, y q a)) := by
          exact mul_le_mul_of_nonneg_right
            (by simpa using Real.sqrt_le_sqrt hC)
            (Real.sqrt_nonneg _)
    _ = Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => ∑ a : OutcomeA, y q a)) := by ring
    _ = Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDCore ψ (A q) (B q))) := by rw [hy_eq]
    _ ≤ Real.sqrt γ := by
          simpa using Real.sqrt_le_sqrt hAB
