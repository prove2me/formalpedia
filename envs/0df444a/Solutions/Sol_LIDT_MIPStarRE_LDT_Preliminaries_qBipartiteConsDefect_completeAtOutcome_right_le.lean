-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Preliminaries.qBipartiteConsDefect_completeAtOutcome_right_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:06:53.149849+00:00
-- url     : https://prove2.me/submissions/076eda17-9f67-4167-a9c8-adfd2a2bfcad

-- Generated proof for MIPStarRE.LDT.Preliminaries.qBipartiteConsDefect_completeAtOutcome_right_le.
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
    {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB))
    (A : _root_.LIDT.MIPStarRE.LDT.Measurement Outcome ιA)
    (B : _root_.LIDT.MIPStarRE.LDT.SubMeas Outcome ιB)
    (a0 : Outcome) :
    _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome B a0).toSubMeas ≤
      _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas B +
        _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) (1 - B.total)) := by
  classical
  let R : _root_.LIDT.MIPStarRE.Quantum.Op ιB := 1 - B.total
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact sub_nonneg.mpr B.total_le_one
  have hmatchExtra_nonneg : 0 ≤ _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a0) R) := by
    exact _root_.LIDT.MIPStarRE.LDT.ev_nonneg_of_psd ψ _ <|
      (Matrix.PosSemidef.kronecker
        (Matrix.nonneg_iff_posSemidef.mp (A.toSubMeas.outcome_pos a0))
        (Matrix.nonneg_iff_posSemidef.mp hR_nonneg)).nonneg
  have hmatch :
      _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass ψ A.toSubMeas (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome B a0).toSubMeas =
        _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass ψ A.toSubMeas B + _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a0) R) := by
    unfold _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass
    calc
      ∑ a : Outcome,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.opTensor (A.toSubMeas.outcome a) ((_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome B a0).toSubMeas.outcome a))
        = ∑ a : Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a) (B.outcome a + if a = a0 then R else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              by_cases ha : a = a0 <;> simp [_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome, ha, R]
      _ = ∑ a : Outcome,
            (_root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a) (B.outcome a)) +
              _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a) (if a = a0 then R else 0))) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              by_cases ha : a = a0
              · simp [ha, _root_.LIDT.MIPStarRE.LDT.opTensor, _root_.LIDT.MIPStarRE.LDT.ev_add, Matrix.kronecker_add]
              · simpa [ha, _root_.LIDT.MIPStarRE.LDT.opTensor] using (_root_.LIDT.MIPStarRE.LDT.ev_zero ψ)
      _ = _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass ψ A.toSubMeas B +
            ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a) (if a = a0 then R else 0)) := by
              simp [_root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass, Finset.sum_add_distrib]
      _ = _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass ψ A.toSubMeas B + _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a0) R) := by
              rw [Finset.sum_eq_single a0]
              · simp [R]
              · intro a _ ha
                simpa [ha, _root_.LIDT.MIPStarRE.LDT.opTensor] using (_root_.LIDT.MIPStarRE.LDT.ev_zero ψ)
              · intro hnot
                exact (hnot (Finset.mem_univ a0)).elim
  have htotal :
      _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor A.toSubMeas.total ((_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome B a0).toSubMeas.total)) =
        _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor A.toSubMeas.total B.total) + _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) R) := by
    calc
      _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor A.toSubMeas.total ((_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome B a0).toSubMeas.total))
        = _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B.total + R)) := by
            simp [_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome, A.total_eq_one, R]
      _ = _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.opTensor (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) B.total +
              _root_.LIDT.MIPStarRE.LDT.opTensor (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) R) := by
              congr 1
              simp [_root_.LIDT.MIPStarRE.LDT.opTensor, Matrix.kronecker_add]
      _ = _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) B.total) +
            _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) R) := by
              rw [_root_.LIDT.MIPStarRE.LDT.ev_add]
      _ = _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor A.toSubMeas.total B.total) +
            _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) R) := by
              simp [A.total_eq_one]
      _ = _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor A.toSubMeas.total B.total) + _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) R) := by
            rfl
  have hinnerB_le :
      _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor A.toSubMeas.total B.total) - _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass ψ A.toSubMeas B ≤
        _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas B := by
    exact le_max_right 0 _
  have hinnerC_le :
      _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor A.toSubMeas.total ((_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome B a0).toSubMeas.total)) -
          _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass ψ A.toSubMeas (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome B a0).toSubMeas ≤
        _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas B + _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) R) := by
    rw [htotal, hmatch]
    linarith
  have hrhs_nonneg :
      0 ≤ _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas B + _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) R) := by
    have hright_nonneg : 0 ≤ _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) R) :=
      _root_.LIDT.MIPStarRE.LDT.ev_nonneg_of_psd ψ _ <|
        (Matrix.nonneg_iff_posSemidef.mp (_root_.LIDT.MIPStarRE.LDT.rightTensor_nonneg (ι₁ := ιA) hR_nonneg)).nonneg
    exact add_nonneg (_root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect_nonneg ψ A.toSubMeas B) hright_nonneg
  unfold _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect
  exact max_le_iff.mpr ⟨hrhs_nonneg, hinnerC_le⟩
