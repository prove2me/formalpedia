-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.mainFormalError_ge_one_of_q_lt_d
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:52:16.1563+00:00
-- url     : https://prove2.me/submissions/e2f23148-d0a6-43d8-b007-9330d9d3c9f0

-- Generated proof for MIPStarRE.LDT.Test.mainFormalError_ge_one_of_q_lt_d.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_ProjectivizationChain_Basic
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_mainFormalError_ge_one_of_one_le_envelope

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.LDT.Test
end LIDT.MIPStarRE.LDT.Test

namespace LIDT

end LIDT

open LIDT
/-!
# Main-formal scalar bounds

Scalar estimates for the two-space `mainFormal` theorem.  This module defines
the five scalars that appear in the paper's error calculation:

* `σ` — the symmetrized induction consistency error
* `ζ₁` — the cross-consistency error after unsymmetrization
* `ζ₂` — the orthonormalize-and-complete closeness error
* `ζ₃` — the projective self-consistency error
* `ζ₄` — the final point-consistency error

The core structure `MainFormalScalarBounds` (Prop) bundles the three
hypotheses needed to invoke the checked Step 8 bound
`errorCascade_le_mainFormalError`:

* `cascadeHypotheses` — the standing scalar regime (`q > 0`, `k ≥ 1`,
  `m ≥ 1`, `0 ≤ ε ≤ 1`, `d ≤ q`).
* `inductionNu_nonneg` — nonnegativity of the symmetrized main-induction
  `ν` at `(3ε, 3ε, 3ε)`.
* `inductionNu_bound` — the paper line 71–73 coarsening
  `ν ≤ 10000 k² m² (ε^{1/1024} + (d/q)^{1/1024})`.

The cascade comparisons `ζ₁ ≤ …`, `ζ₃ ≤ 2·mainFormalError`, etc. are then
derived in the private theorem `cascadeBounds` via
`errorCascade_le_mainFormalError`, which calls the already-formalized
scalar cascade estimates from `LDT.Test.MainTheorem.ScalarBounds`.  The module also
provides the vacuous-branch analysis (`mainFormalError_ge_one_of_*`) and
the coarsening lemma that absorbs `orthonormalizeAndCompleteError` into
`ζ₂` (`orthonormalizeAndCompleteError_zeta1_le_zeta2`).

## References

* Paper: `references/ldt-paper/inductive_step.tex`,
  error computations (lines 68–75, 186–234).
* Blueprint: `blueprint/src/chapter/ch10_induction.tex`,
  `\label{def:main-formal-error-cascade}`,
  `\label{thm:sigma-bound-main-formal}`, and
  `\label{thm:zeta-bounds-main-formal}`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

open LIDT.MIPStarRE.LDT.Test

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) (k : ℕ) (eps : _root_.LIDT.MIPStarRE.LDT.Error)
    (hk0 : 0 < k) (hepsNN : 0 ≤ eps)
    (hqd : (params.q : _root_.LIDT.MIPStarRE.LDT.Error) < (params.d : _root_.LIDT.MIPStarRE.LDT.Error)) :
    1 ≤ _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError params k eps := by
  have hdq_gt_one : 1 < (params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) := by
    exact (one_lt_div params.q_cast_pos).2 hqd
  have hdqPow : 1 ≤ Real.rpow ((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))
      (1 / (40000 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
    exact Real.one_le_rpow hdq_gt_one.le (by positivity)
  have hepsPowNN : 0 ≤ Real.rpow eps (1 / (40000 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
    Real.rpow_nonneg hepsNN _
  have hExpNN :
      0 ≤ Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (2560000 * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ))))) :=
    Real.exp_nonneg _
  have henv : 1 ≤ _root_.LIDT.MIPStarRE.LDT.Test.mainFormalEnvelope params k eps := by
    unfold _root_.LIDT.MIPStarRE.LDT.Test.mainFormalEnvelope
    linarith
  exact _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError_ge_one_of_one_le_envelope params k eps hk0 henv
