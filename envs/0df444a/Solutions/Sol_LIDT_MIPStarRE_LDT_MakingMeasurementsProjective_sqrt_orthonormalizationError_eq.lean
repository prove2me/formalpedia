-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.sqrt_orthonormalizationError_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:14:56.923986+00:00
-- url     : https://prove2.me/submissions/cbb7cf6e-cd43-4429-a259-d8b692349956

-- Generated proof for MIPStarRE.LDT.MakingMeasurementsProjective.sqrt_orthonormalizationError_eq.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_LayerAlgebra
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Rows
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_ProjectorApprox
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_AlmostProjective
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_TruncationCombinatorics
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_LdtSimp
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_LdtSimpAttr
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_LIDT_MIPStarRE_Quantum_ProjectorONB
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic.Attr.Register

namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Section 5 — basic projectivization data

This module contains the scalar estimates and elementary transport lemmas used
by the orthonormalization projectivization chain.  The mathematical source is the
orthonormalization-and-completion argument in `inductive_step.tex`, lines
130--149, together with the orthonormalization theorem and the completion
proposition cited there.

The declarations here are deliberately prior to the construction of the final
projective measurements.  They record the literal scalar obtained by composing
orthonormalization with completion, its absorbed form in the unit-error regime,
the right-register transport available under permutation invariance, and the
residual hypotheses passed to the self-consistency handoff theorem.  The actual
projective-measurement output theorem is in `ProjectivizationChain.Output`.

The scalar computation is

    ζ₂ = 2 · (100·ζ^{1/4}) + 4 · √(100·ζ^{1/4}) + 2·ζ
       = 200·ζ^{1/4} + 40·ζ^{1/8} + 2·ζ.

The paper prints the closed form `ζ₂ = 200·ζ^{1/4} + 40·ζ^{1/8}`.  The Lean
cascade uses the slightly widened absorbed scalar
`200·ζ^{1/4} + 42·ζ^{1/8}` downstream, since in the non-vacuous regime
`0 ≤ ζ ≤ 1` gives `2·ζ ≤ 2·ζ^{1/8}`.

## Status

- The orthonormalization step uses the source theorem `orthonormalization`.
  The theorem has a tracked proof gap for the sharp paper constant; this file
  no longer exposes its proof-stage construction data as a hypothesis of the
  orthonormalization projectivization output statement.
- The completion step uses the **fully-formalized** `completingToMeasurement`
  (`\leanok` in `blueprint/src/chapter/ch03_preliminaries.tex`), so no new
  bridge is introduced here.
- The output `Q` is now a `ProjMeas`. This uses the generic helper
  `Preliminaries.completeAtOutcomeProj`, whose proof relies only on the
  existing facts that `P.total` is a projection and that each `P_a` is
  absorbed by `P.total`.

## References

- Paper: `references/ldt-paper/inductive_step.tex` lines 130–149
  (application of `lem:orthonormalization-main-lemma` +
  `prop:completing-to-measurement`).
- Paper: `references/ldt-paper/orthonormalization.tex` lines 67–77
  (`thm:orthonormalization`).
- Paper: `references/ldt-paper/preliminaries.tex` lines 1101–1170
  (`prop:completing-to-measurement`).
- Blueprint: `blueprint/src/chapter/ch10_induction.tex` lines 350–360
  (`eq:G-with-Q-A`).
- Blueprint: `blueprint/src/chapter/ch04_projective.tex`
  (orthonormalization theorem).
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-! ### Error functions -/

theorem solution {ζ : _root_.LIDT.MIPStarRE.LDT.Error} (hζ0 : 0 ≤ ζ) :
    Real.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationError ζ) = 10 * Real.rpow ζ (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
  have hsqrt100 : Real.sqrt (100 : _root_.LIDT.MIPStarRE.LDT.Error) = 10 := by
    rw [← Real.sqrt_sq (show (0 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 10 by norm_num)]
    norm_num
  have hsqrtRpow : Real.sqrt (Real.rpow ζ (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) =
      Real.rpow ζ (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    rw [Real.sqrt_eq_rpow]
    calc
      Real.rpow (Real.rpow ζ (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error))
          = Real.rpow ζ ((1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) * (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error))) := by
              simpa using
                (Real.rpow_mul hζ0 (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error))).symm
      _ = Real.rpow ζ (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) := by norm_num
  unfold _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationError
  calc
    Real.sqrt (100 * Real.rpow ζ (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)))
        = Real.sqrt (100 : _root_.LIDT.MIPStarRE.LDT.Error) *
            Real.sqrt (Real.rpow ζ (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) := by
            rw [Real.sqrt_mul (by norm_num : 0 ≤ (100 : Error))]
    _ = 10 * Real.rpow ζ (1 / (8 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
        rw [hsqrt100, hsqrtRpow]
