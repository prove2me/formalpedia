-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Preliminaries.evaluateAt_completeAtOutcome
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:03:35.680102+00:00
-- url     : https://prove2.me/submissions/9f8ed7fc-4c98-449a-ac0d-09dee7663e6e

-- Generated proof for MIPStarRE.LDT.Preliminaries.evaluateAt_completeAtOutcome.
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
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (H : _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ι)
    (h0 : _root_.LIDT.MIPStarRE.LDT.Polynomial params)
    (u : _root_.LIDT.MIPStarRE.LDT.Point params) :
    _root_.LIDT.MIPStarRE.LDT.evaluateAt params u (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome H h0).toSubMeas =
      (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome (_root_.LIDT.MIPStarRE.LDT.evaluateAt params u H) (h0 u)).toSubMeas := by
  classical
  let R : _root_.LIDT.MIPStarRE.Quantum.Op ι := 1 - H.total
  let L := _root_.LIDT.MIPStarRE.LDT.evaluateAt params u (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome H h0).toSubMeas
  let Rhs := (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome (_root_.LIDT.MIPStarRE.LDT.evaluateAt params u H) (h0 u)).toSubMeas
  have houtcome : L.outcome = Rhs.outcome := by
    funext b
    let S : Finset (_root_.LIDT.MIPStarRE.LDT.Polynomial params) :=
      Finset.univ.filter fun h : _root_.LIDT.MIPStarRE.LDT.Polynomial params => h u = b
    have hsplit :
        (∑ h ∈ S,
            if hh : h = h0 then H.outcome h + R else H.outcome h) =
          (∑ h ∈ S, H.outcome h) +
            ∑ h ∈ S, if h = h0 then R else 0 := by
      calc
        (∑ h ∈ S, if hh : h = h0 then H.outcome h + R else H.outcome h)
          = ∑ h ∈ S, (H.outcome h + if h = h0 then R else 0) := by
              refine Finset.sum_congr rfl ?_
              intro h hh
              by_cases hEq : h = h0 <;> simp [hEq]
        _ = (∑ h ∈ S, H.outcome h) + ∑ h ∈ S, if h = h0 then R else 0 := by
              rw [Finset.sum_add_distrib]
    have hresidual :
        (∑ h ∈ S, if h = h0 then R else 0) =
          if b = h0 u then R else 0 := by
      rw [Finset.sum_ite_eq' S h0 (fun _ => R)]
      by_cases hb : b = h0 u <;> simp [S, hb, eq_comm]
    have hLout :
        (_root_.LIDT.MIPStarRE.LDT.evaluateAt params u (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome H h0).toSubMeas).outcome b =
          ∑ h ∈ Finset.univ.filter (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g u = b),
            (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome H h0).toSubMeas.outcome h := by
      ext i j
      simp only [_root_.LIDT.MIPStarRE.LDT.evaluateAt, _root_.LIDT.MIPStarRE.LDT.postprocess]
    have hEval :
        (_root_.LIDT.MIPStarRE.LDT.evaluateAt params u H).outcome b =
          ∑ h ∈ Finset.univ.filter (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g u = b), H.outcome h := by
      ext i j
      simp only [_root_.LIDT.MIPStarRE.LDT.evaluateAt, _root_.LIDT.MIPStarRE.LDT.postprocess]
    calc
      L.outcome b = ∑ h ∈ S, if hh : h = h0 then H.outcome h + R else H.outcome h := by
              simpa [L, S, _root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome, R] using hLout
      _ = (∑ h ∈ S, H.outcome h) + ∑ h ∈ S, if h = h0 then R else 0 := hsplit
      _ = (_root_.LIDT.MIPStarRE.LDT.evaluateAt params u H).outcome b + if b = h0 u then R else 0 := by
            rw [hEval]
            exact congrArg (fun X => (∑ h ∈ S, H.outcome h) + X) hresidual
      _ = Rhs.outcome b := by
            by_cases hb : b = h0 u
            · simp [Rhs, _root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome, hb, R, _root_.LIDT.MIPStarRE.LDT.evaluateAt, _root_.LIDT.MIPStarRE.LDT.postprocess_total]
            · simp [Rhs, _root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome, hb, R, _root_.LIDT.MIPStarRE.LDT.evaluateAt, _root_.LIDT.MIPStarRE.LDT.postprocess_total]
  have htotal : L.total = Rhs.total := by
    simp [L, Rhs, _root_.LIDT.MIPStarRE.LDT.evaluateAt, _root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome, _root_.LIDT.MIPStarRE.LDT.postprocess]
  exact _root_.LIDT.MIPStarRE.LDT.SubMeas.ext (A := L) (B := Rhs) (fun a => congrFun houtcome a) htotal
