-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToG_sum_finsets_by_card_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:29:29.166117+00:00
-- url     : https://prove2.me/submissions/004410b9-7112-455c-ab5d-0add0af26b94

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToG_sum_finsets_by_card_indicator.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
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
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting

namespace LIDT

end LIDT

open LIDT
/-!
# Section 12 pasting: Bernoulli tail polynomial combinatorics

Finset re-indexing and cardinality-grouping lemmas for the Bernoulli-tail
operator endpoint of the `fromHToG` recurrence.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (G : _root_.LIDT.MIPStarRE.Quantum.Op ι) (d k : ℕ) :
    (∑ s : Finset (Fin k),
        if d + 1 ≤ s.card then G ^ s.card * (1 - G) ^ (k - s.card) else 0) =
      ∑ r ∈ Finset.Icc (d + 1) k,
        (Nat.choose k r : ℂ) • (G ^ r * (1 - G) ^ (k - r)) := by
  classical
  let F : ℕ → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun r =>
    if d + 1 ≤ r then G ^ r * (1 - G) ^ (k - r) else 0
  have hpow := Finset.sum_powerset_apply_card (x := (Finset.univ : Finset (Fin k))) F
  have hleft :
      (∑ s : Finset (Fin k), F s.card) =
        ∑ s ∈ (Finset.univ : Finset (Fin k)).powerset, F s.card := by
    rw [Finset.powerset_univ]
  calc
    (∑ s : Finset (Fin k),
        if d + 1 ≤ s.card then G ^ s.card * (1 - G) ^ (k - s.card) else 0)
      = ∑ s : Finset (Fin k), F s.card := by rfl
    _ = ∑ s ∈ (Finset.univ : Finset (Fin k)).powerset, F s.card := hleft
    _ = ∑ r ∈ Finset.range ((Finset.univ : Finset (Fin k)).card + 1),
          (Finset.univ : Finset (Fin k)).card.choose r • F r := hpow
    _ = ∑ r ∈ Finset.range (k + 1), Nat.choose k r • F r := by simp
    _ = ∑ r ∈ Finset.Icc (d + 1) k, Nat.choose k r • F r := by
      symm
      refine Finset.sum_subset ?hsubset ?hzero
      · intro r hr
        simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢
        exact Nat.lt_succ_of_le hr.2
      · intro r hrange hrnot
        simp only [Finset.mem_range, Finset.mem_Icc] at hrange hrnot
        have hnot : ¬ d + 1 ≤ r := by
          intro hdr
          exact hrnot ⟨hdr, Nat.le_of_lt_succ hrange⟩
        dsimp [F]
        rw [if_neg hnot]
        simp
    _ = ∑ r ∈ Finset.Icc (d + 1) k,
        (Nat.choose k r : ℂ) • (G ^ r * (1 - G) ^ (k - r)) := by
      refine Finset.sum_congr rfl ?_
      intro r hr
      simp only [Finset.mem_Icc] at hr
      have hdr : d + 1 ≤ r := hr.1
      dsimp [F]
      rw [if_pos hdr]
      simp [Algebra.smul_def]
