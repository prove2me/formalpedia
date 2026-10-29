-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.ldPastingNontrivial
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T18:18:37.806875+00:00
-- url     : https://prove2.me/submissions/4e624d3f-124d-45e7-a464-6b492f23e9de

-- Generated proof for MIPStarRE.LDT.Pasting.ldPastingNontrivial.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_Chain_FinalMove
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_Chain_HalfSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_StageA0M1
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_BernoulliTail
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_FactBundles
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_MoveLemmas_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_PaperBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadMass
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_NonglobalDecomposition
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_bernoulliTailOperator_leftTensor
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_chernoffBernoulliMatrix
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_hAConsistency_completed_from_submeas
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_hAConsistency_submeas
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_ldPastingNCompleteness_of_tailLowerBound

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

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/Final.lean. -/
/-!
# Section 12 pasting: final pasting theorems

Final completeness and pasting theorems.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



/-- Paper arithmetic: for `θ = 1/(200m)`,
`1/(1-θ) ≤ 1 + 1/(100m)`. -/
private lemma ldPasting_theta_inv_le (params : Parameters) :
    (1 / (1 - 1 / (200 * (params.m : Error))) : Error) ≤
      1 + 1 / (100 * (params.m : Error)) := by
  have hm_pos : (0 : Error) < (params.m : Error) := by exact_mod_cast params.hm
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast (Nat.succ_le_of_lt params.hm)
  have hden200_pos : 0 < 200 * (params.m : Error) := by positivity
  have hden100_pos : 0 < 100 * (params.m : Error) := by positivity
  have hdenMinus_pos : 0 < 200 * (params.m : Error) - 1 := by nlinarith
  have hdenMinus_ge : 100 * (params.m : Error) ≤ 200 * (params.m : Error) - 1 := by
    nlinarith
  calc
    (1 / (1 - 1 / (200 * (params.m : Error))) : Error)
        = (200 * (params.m : Error)) / (200 * (params.m : Error) - 1) := by
            field_simp [hden200_pos.ne', hdenMinus_pos.ne']
    _ = 1 + 1 / (200 * (params.m : Error) - 1) := by
            field_simp [hdenMinus_pos.ne']
            nlinarith
    _ ≤ 1 + 1 / (100 * (params.m : Error)) := by
            gcongr

/-- Paper arithmetic: the matrix-Chernoff exponential at `θ = 1/(200m)` is the
stated `exp(-k/(80000m²))` term. -/
private lemma ldPasting_chernoff_exponent_eq (params : Parameters) (k : ℕ) :
    -(((1 / (200 * (params.m : Error))) ^ (2 : ℕ)) * (k : Error)) / 2 =
      -((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))) := by
  have hm_pos : (0 : Error) < (params.m : Error) := by exact_mod_cast params.hm
  have hden_pos : (0 : Error) < 200 * (params.m : Error) := by positivity
  have hden2_pos : (0 : Error) < 80000 * ((params.m : Error) ^ (2 : ℕ)) := by positivity
  field_simp [hden_pos.ne', hden2_pos.ne']
  ring

/-- The public size assumption `k ≥ 400md` implies the matrix-Chernoff size
condition `k ≥ 2d/θ` at `θ = 1/(200m)`. -/
private lemma ldPasting_chernoff_size (params : Parameters) (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    (2 * (params.d : Error)) / (1 / (200 * (params.m : Error))) ≤ (k : Error) := by
  have hm_pos : (0 : Error) < (params.m : Error) := by exact_mod_cast params.hm
  have hden_pos : (0 : Error) < 200 * (params.m : Error) := by positivity
  have hkE : (400 * params.m * params.d : Error) ≤ (k : Error) := by exact_mod_cast hk
  field_simp [hden_pos.ne']
  nlinarith

/-- Specialize `lem:chernoff-bernoulli-matrix` to the averaged complete operator
`G = 𝔼_x ∑_g G^x_g` and the paper's `θ = 1/(200m)`.

This is the previously residual Bernoulli-tail lower-bound step in
`cor:ld-pasting-N-completeness`: the matrix Chernoff lemma is applied on the left
register to `G ⊗ I`, then `bernoulliTailOperator_leftTensor` identifies its
conclusion and swap-invariance transfers it to the paper-shaped right-register
`fromHToGBernoulliTailMass`. -/
private lemma fromHToGBernoulliTailMass_lower_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (kappa : Error)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    1 - kappa * (1 + 1 / (100 * (params.m : Error))) -
        Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) ≤
      fromHToGBernoulliTailMass params strategy.state family k := by
  let G : MIPStarRE.Quantum.Op ι := (IdxPolyFamily.averagedSubMeas family).total
  let X : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) G
  have hGpsd : 0 ≤ G := (IdxPolyFamily.averagedSubMeas family).total_nonneg
  have hGle : G ≤ 1 := (IdxPolyFamily.averagedSubMeas family).total_le_one
  have hXpsd : 0 ≤ X := by
    dsimp [X]
    exact leftTensor_nonneg (ι₂ := ι) hGpsd
  have hXle : X ≤ 1 := by
    dsimp [X]
    exact leftTensor_le_one (ι₂ := ι) hGle
  have hbase :
      CompletenessAtLeast strategy.state
        (SubMeas.singleOutcome X hXpsd hXle)
        (1 - kappa) := by
    refine ⟨?_⟩
    simpa [subMeasMass, X, G, SubMeas.liftLeft] using hcomplete.averageCompleteness.lowerBound
  have htheta_pos : (0 : Error) < 1 / (200 * (params.m : Error)) := by
    have hm_pos : (0 : Error) < (params.m : Error) := by exact_mod_cast params.hm
    positivity
  have htheta_lt_one : (1 / (200 * (params.m : Error)) : Error) < 1 := by
    have hm_pos : (0 : Error) < (params.m : Error) := by exact_mod_cast params.hm
    have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
      exact_mod_cast (Nat.succ_le_of_lt params.hm)
    have hden_pos : (0 : Error) < 200 * (params.m : Error) := by positivity
    field_simp [hden_pos.ne']
    nlinarith
  have hchern := chernoffBernoulliMatrix strategy.state strategy.isNormalized
    (1 / (200 * (params.m : Error))) k params.d X kappa
    htheta_pos htheta_lt_one (ldPasting_chernoff_size params k hk) hXpsd hXle
    (by simpa [SubMeas.singleOutcome] using hbase)
  have hmassLower := hchern.matrixTailBound.lowerBound
  have hmass_eq :
      subMeasMass strategy.state
        (bernoulliTailSubMeas k params.d X hXpsd hXle) =
        fromHToGBernoulliTailMass params strategy.state family k := by
    have hswap :
        ev strategy.state
            (leftTensor (ι₂ := ι)
              (bernoulliTailOperator k params.d family.averagedSubMeas.total)) =
          ev strategy.state
            (rightTensor (ι₁ := ι)
              (bernoulliTailOperator k params.d family.averagedSubMeas.total)) :=
      strategy.permInvState.swap_ev _
    simp [fromHToGBernoulliTailMass, bernoulliTailFromFamily, subMeasMass,
      IdxSubMeas.liftRight, constSubMeasFamily, X, G, bernoulliTailOperator_leftTensor,
      hswap]
  have htailMass :
      1 - kappa / (1 - 1 / (200 * (params.m : Error))) -
          Real.exp (-(((1 / (200 * (params.m : Error))) ^ (2 : ℕ)) * (k : Error)) / 2) ≤
        fromHToGBernoulliTailMass params strategy.state family k := by
    simpa [hmass_eq] using hmassLower
  have hmass_le_one : subMeasMass strategy.state family.averagedSubMeas.liftLeft ≤ 1 := by
    unfold subMeasMass SubMeas.liftLeft
    have hle : leftTensor (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total ≤
        (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
      exact leftTensor_le_one (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total_le_one
    simpa [ev_one_of_isNormalized strategy.state strategy.isNormalized] using
      ev_mono strategy.state _ _ hle
  have hkappa_nonneg : 0 ≤ kappa := by
    have hlower := hcomplete.averageCompleteness.lowerBound
    have hupper := hmass_le_one
    linarith
  have hcoef :
      kappa / (1 - 1 / (200 * (params.m : Error))) ≤
        kappa * (1 + 1 / (100 * (params.m : Error))) := by
    have := mul_le_mul_of_nonneg_left (ldPasting_theta_inv_le params) hkappa_nonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hexp :
      Real.exp (-(((1 / (200 * (params.m : Error))) ^ (2 : ℕ)) * (k : Error)) / 2) =
        Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
    rw [ldPasting_chernoff_exponent_eq]
  linarith



-- The downstream completeness theorem elaborates the full `fromHToG` reduction facts.


/-- `cor:ld-pasting-N-completeness`. -/
theorem ldPastingNCompleteness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    LdPastingNCompletenessStatement params strategy family kappa
      (MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) k := by
  have htail :
      1 - kappa * (1 + 1 / (100 * (params.m : Error))) -
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) ≤
        fromHToGBernoulliTailMass params strategy.state family k := by
    exact fromHToGBernoulliTailMass_lower_bound params strategy kappa family hcomplete k hk
  exact ldPastingNCompleteness_of_tailLowerBound params strategy
    eps delta gamma kappa zeta hgood hgamma_le hzeta_le hdq_le hd
    family hcons hself hbound k hk_pos hk htail

























end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/HAConsistency.lean. -/
/-!
# Section 12 pasting: H-A consistency

Vertical-line to point-consistency transport and completed-measurement statement for
`cor:h-a-consistency`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

















/-- Completed-measurement version of `cor:h-a-consistency`.

This theorem is intentionally downstream of `cor:ld-pasting-N-completeness`:
it may use the submeasurement consistency together with the completeness bound
for the constructed pasted submeasurement to control the added completion mass. -/
theorem hAConsistency_completed
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (family : IdxPolyFamily params ι)
    (k : ℕ)
    (hsubmeas :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta))
    (hcomplete :
      CompletenessAtLeast strategy.state
        (constructedPastedSubMeas params family k).liftLeft
        (ldPastingCompletenessLowerBound params kappa
          (MainInductionStep.ldPastingInInductionNu params k
            eps delta gamma zeta) k)) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (constructedPastedMeasurement params family k).toSubMeas)
      (MainInductionStep.ldPastingInInductionError params k
        eps delta gamma kappa zeta) := by
  simpa [constructedPastedMeasurement] using
    hAConsistency_completed_from_submeas params strategy eps delta gamma kappa zeta
      (constructedPastedSubMeas params family k) k hsubmeas hcomplete

end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: final pasting theorems

Final completeness and pasting theorems.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]













-- The downstream completeness theorem elaborates the full `fromHToG` reduction facts.

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (eps delta gamma kappa zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : _root_.LIDT.MIPStarRE.LDT.Measurement (_root_.LIDT.MIPStarRE.LDT.Polynomial params.next) ι,
      H = _root_.LIDT.MIPStarRE.LDT.Pasting.constructedPastedMeasurement params family k ∧
        _root_.LIDT.MIPStarRE.LDT.Pasting.LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  refine ⟨_root_.LIDT.MIPStarRE.LDT.Pasting.constructedPastedMeasurement params family k, rfl, ?_⟩
  have hsubmeasConsistency :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.hAConsistency_submeas params strategy eps delta gamma zeta
      hgood hgamma_le hzeta_le hdq_le hd
      family hcons hself hbound k hk_pos
  have hcompleteness :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.ldPastingNCompleteness params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le hd
      family hcomplete hcons hself hbound k hk_pos hk
  have hconsistency :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.hAConsistency_completed params strategy eps delta gamma kappa zeta
      family k hsubmeasConsistency hcompleteness.completenessBound
  exact
    { pointConsistency := hconsistency }
