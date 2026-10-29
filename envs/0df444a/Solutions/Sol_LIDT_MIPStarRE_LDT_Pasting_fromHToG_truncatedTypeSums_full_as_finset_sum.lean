-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToG_truncatedTypeSums_full_as_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:29:29.269754+00:00
-- url     : https://prove2.me/submissions/8578509c-63ed-4612-a408-323498d42c5b

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToG_truncatedTypeSums_full_as_finset_sum.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_BernoulliTail
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

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core/BernoulliTail.lean. -/
/-!
# Section 12 pasting: Bernoulli tail polynomial combinatorics

Finset re-indexing and cardinality-grouping lemmas for the Bernoulli-tail
operator endpoint of the `fromHToG` recurrence.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



lemma fromHToG_gHatTypeWeight_of_finset {k : ℕ} (s : Finset (Fin k)) :
    gHatTypeWeight (fun i : Fin k => i ∈ s) = s.card := by
  simp [gHatTypeWeight]

lemma fromHToG_gHatTypeOperator_of_finset
    (G : MIPStarRE.Quantum.Op ι) {k : ℕ} (s : Finset (Fin k)) :
    gHatTypeOperator G (fun i : Fin k => i ∈ s) =
      G ^ s.card * (1 - G) ^ (k - s.card) := by
  simp [gHatTypeOperator, fromHToG_gHatTypeWeight_of_finset]









end MIPStarRE.LDT.Pasting

end

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
    _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d k (default : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType 0) =
      ∑ s : Finset (Fin k),
        if d + 1 ≤ s.card then G ^ s.card * (1 - G) ^ (k - s.card) else 0 := by
  unfold _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums
  calc
    (∑ τprefix : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType k,
      if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τprefix + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (default : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType 0) then
        _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G τprefix
      else 0)
      = ∑ s : Finset (Fin k),
          if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeFinsetEquiv k).symm s) +
              _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (default : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType 0) then
            _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeFinsetEquiv k).symm s)
          else 0 := by
          exact Fintype.sum_equiv (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeFinsetEquiv k)
            (fun τ => if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τ +
                _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (default : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType 0) then
              _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G τ
            else 0)
            (fun s => if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeFinsetEquiv k).symm s) +
                _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (default : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType 0) then
              _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G ((_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeFinsetEquiv k).symm s)
            else 0)
            (by intro τ; simp)
    _ = ∑ s : Finset (Fin k),
        if d + 1 ≤ s.card then G ^ s.card * (1 - G) ^ (k - s.card) else 0 := by
        refine Finset.sum_congr rfl ?_
        intro s _
        simp [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeFinsetEquiv, _root_.LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatTypeOperator_of_finset, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight]
