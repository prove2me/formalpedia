-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Preliminaries.completion_self_distance
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:03:35.452241+00:00
-- url     : https://prove2.me/submissions/57b9c82a-c8d0-42db-bb98-3cc2d98bb9aa

-- Generated proof for MIPStarRE.LDT.Preliminaries.completion_self_distance.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Preliminary comparison theorems: bipartite self-consistency (completion)

Completion-transfer lemmas for bipartite self-consistency.  The constant
`Unit`-family reductions identify `sddError` and `sscError` with their pointwise
forms, and the later lemmas compare a submeasurement with its completion.

## References

- `references/ldt-paper/preliminaries.tex`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

theorem solution
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState ι) (B : _root_.LIDT.MIPStarRE.LDT.SubMeas Outcome ι) (a0 : Outcome) :
    _root_.LIDT.MIPStarRE.LDT.qSDD ψ B (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome B a0).toSubMeas =
      _root_.LIDT.MIPStarRE.LDT.ev ψ (((1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) - B.total) *
        ((1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) - B.total)) := by
  classical
  let R : _root_.LIDT.MIPStarRE.Quantum.Op ι := 1 - B.total
  have hsum :
      ∑ a : Outcome,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            ((B.outcome a -
                (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome B a0).toSubMeas.outcome a)ᴴ *
              (B.outcome a -
                (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome B a0).toSubMeas.outcome a)) =
        _root_.LIDT.MIPStarRE.LDT.ev ψ (R * R) := by
    have hBtotal_herm : B.totalᴴ = B.total := by
      exact (Matrix.nonneg_iff_posSemidef.mp B.total_nonneg).isHermitian.eq
    have hsingle :
        ∑ a : Outcome,
          (if a = a0 then _root_.LIDT.MIPStarRE.LDT.ev ψ (R * R) else 0) =
          _root_.LIDT.MIPStarRE.LDT.ev ψ (R * R) := by
      simp
    calc
      ∑ a : Outcome,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            ((B.outcome a -
                (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome B a0).toSubMeas.outcome a)ᴴ *
              (B.outcome a -
                (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome B a0).toSubMeas.outcome a))
        = ∑ a : Outcome, if a = a0 then _root_.LIDT.MIPStarRE.LDT.ev ψ (R * R) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases ha : a = a0
            · subst ha
              have hRflip :
                  (B.total - 1) * (B.total - 1) =
                    (1 - B.total) * (1 - B.total) := by
                noncomm_ring
              simp [_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome, R, hBtotal_herm, hRflip]
            · simp [_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome, ha, _root_.LIDT.MIPStarRE.LDT.ev_zero]
      _ = _root_.LIDT.MIPStarRE.LDT.ev ψ (R * R) := hsingle
  simpa [_root_.LIDT.MIPStarRE.LDT.qSDD, _root_.LIDT.MIPStarRE.LDT.qSDDCore, R] using hsum
