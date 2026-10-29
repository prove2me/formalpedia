-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Preliminaries.qSDDOp_symm
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:11:32.901589+00:00
-- url     : https://prove2.me/submissions/30a4a20b-78c4-45a6-b944-61b1a3bbd22c

-- Generated proof for MIPStarRE.LDT.Preliminaries.qSDDOp_symm.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
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

namespace LIDT

end LIDT

open LIDT
/-!
# Preliminary comparison theorems: core layer

Core comparison lemmas and measurement-agreement translations for the
preliminaries chapter.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder


open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

theorem solution
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState ι) (A B : _root_.LIDT.MIPStarRE.LDT.OpFamily Outcome ι) :
    _root_.LIDT.MIPStarRE.LDT.qSDDOp ψ A B = _root_.LIDT.MIPStarRE.LDT.qSDDOp ψ B A := by
  let F : Outcome → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun a => A.outcome a - B.outcome a
  let G : Outcome → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun a => B.outcome a - A.outcome a
  have hFG : F = fun a => -G a := by
    funext a
    dsimp [F, G]
    abel
  unfold _root_.LIDT.MIPStarRE.LDT.qSDDOp _root_.LIDT.MIPStarRE.LDT.qSDDCore
  change ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ ((F a)ᴴ * F a) = ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ ((G a)ᴴ * G a)
  rw [hFG]
  refine Finset.sum_congr rfl ?_
  intro a _
  change _root_.LIDT.MIPStarRE.LDT.ev ψ ((-G a)ᴴ * (-G a)) = _root_.LIDT.MIPStarRE.LDT.ev ψ ((G a)ᴴ * G a)
  simp
