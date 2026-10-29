-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.qBipartiteConsDefect_of_measurements
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T18:03:55.390587+00:00
-- url     : https://prove2.me/submissions/7aefc7df-d45b-4a74-bfc6-e7c1d7463419

-- Generated proof for MIPStarRE.LDT.qBipartiteConsDefect_of_measurements.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

end LIDT

open LIDT
/-!
# Role-register algebraic identities for the low individual degree test

Role-pair projection algebra, symmetrized measurement definitions, and expectation
identities for the classical role-register symmetrized state.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

/-! ### Role-pair projection algebra -/

theorem solution {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB))
    (A : _root_.LIDT.MIPStarRE.LDT.Measurement Outcome ιA) (B : _root_.LIDT.MIPStarRE.LDT.Measurement Outcome ιB) :
    _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas =
      _root_.LIDT.MIPStarRE.LDT.ev ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB)) -
        _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas := by
  have hmatch_le :
      _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas ≤
        _root_.LIDT.MIPStarRE.LDT.ev ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB)) := by
    calc
      _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas
        = ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (A.outcome a) (B.outcome a)) := by
            rfl
      _ ≤ ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) (A.outcome a)) := by
            refine Finset.sum_le_sum ?_
            intro a _
            exact _root_.LIDT.MIPStarRE.LDT.ev_mono ψ _ _ <|
              _root_.LIDT.MIPStarRE.LDT.opTensor_le_leftTensor (ι₂ := ιB)
                (A.outcome_pos a) (_root_.LIDT.MIPStarRE.LDT.Measurement.outcome_le_one B a)
      _ = _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) A.total) := by
            rw [← _root_.LIDT.MIPStarRE.LDT.ev_sum ψ (fun a : Outcome => _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) (A.outcome a))]
            rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ιB) Finset.univ A.outcome, A.sum_eq_total]
      _ = _root_.LIDT.MIPStarRE.LDT.ev ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB)) := by
            simp [A.total_eq_one, _root_.LIDT.MIPStarRE.LDT.leftTensor]
  unfold _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect
  rw [show _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor A.toSubMeas.total B.toSubMeas.total) =
      _root_.LIDT.MIPStarRE.LDT.ev ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB)) by
    simp [A.total_eq_one, B.total_eq_one, _root_.LIDT.MIPStarRE.LDT.opTensor]]
  rw [max_eq_right (sub_nonneg.mpr hmatch_le)]
