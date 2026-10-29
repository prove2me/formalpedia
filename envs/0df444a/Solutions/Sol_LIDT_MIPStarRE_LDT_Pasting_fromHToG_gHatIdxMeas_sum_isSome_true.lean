-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.fromHToG_gHatIdxMeas_sum_isSome_true
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:29:28.977672+00:00
-- url     : https://prove2.me/submissions/4f6c9d15-b5bf-4a76-a4e1-a4bc9e73b89c

-- Generated proof for MIPStarRE.LDT.Pasting.fromHToG_gHatIdxMeas_sum_isSome_true.
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
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting

namespace LIDT

end LIDT

open LIDT
/-!
# Section 12 pasting: operator averages and projective submeasurement lemmas

Averages over uniform distributions, tensor placement identities, and
projective submeasurement algebraic lemmas for the `fromHToG` reduction.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) (x : _root_.LIDT.MIPStarRE.LDT.Fq params) :
    (∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = true,
        (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g) =
      (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total := by
  classical
  have hfilter :
      ((Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)).filter fun g => g.isSome = true) =
        (Finset.univ.image (fun p : _root_.LIDT.MIPStarRE.LDT.Polynomial params => (some p : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params))) := by
    ext g
    cases g <;> simp
  calc
    (∑ g ∈ (Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)) with g.isSome = true,
        (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g)
        = ∑ g ∈ ((Finset.univ : Finset (_root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)).filter fun g =>
            g.isSome = true), (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g := by
            rfl
    _ = ∑ g ∈ (Finset.univ.image fun p : _root_.LIDT.MIPStarRE.LDT.Polynomial params =>
            (some p : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatOutcome params)), (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome g := by
          rw [hfilter]
    _ = ∑ p : _root_.LIDT.MIPStarRE.LDT.Polynomial params, (_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas params family x).outcome (some p) := by
          rw [Finset.sum_image]
          intro a _ha b _hb h
          cases h
          rfl
    _ = ∑ p : _root_.LIDT.MIPStarRE.LDT.Polynomial params, (family.meas x).outcome p := by
          simp [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatIdxMeas, _root_.LIDT.MIPStarRE.LDT.completeSubMeas]
    _ = (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total := by
          simp [_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas, _root_.LIDT.MIPStarRE.LDT.postprocess_total, (family.meas x).sum_eq_total]
