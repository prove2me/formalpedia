-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Preliminaries.consRel_uniform_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:06:53.080164+00:00
-- url     : https://prove2.me/submissions/b315334f-3c44-4f08-b56b-9a5b6d2ad23a

-- Generated proof for MIPStarRE.LDT.Preliminaries.consRel_uniform_equiv.
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
    {α β Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (e : α ≃ β)
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB))
    (A : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas α Outcome ιA)
    (B : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas α Outcome ιB)
    (δ : _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) A B δ ↔
      _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β)
        (fun b => A (e.symm b))
        (fun b => B (e.symm b))
        δ := by
  have hEq :
      _root_.LIDT.MIPStarRE.LDT.bipartiteConsError ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) A B =
        _root_.LIDT.MIPStarRE.LDT.bipartiteConsError ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β)
          (fun b => A (e.symm b))
          (fun b => B (e.symm b)) := by
    let f : α → _root_.LIDT.MIPStarRE.LDT.Error := fun a => _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (A a) (B a)
    unfold _root_.LIDT.MIPStarRE.LDT.bipartiteConsError
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) (fun a => _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (A a) (B a))
        = (1 / (Fintype.card α : _root_.LIDT.MIPStarRE.LDT.Error)) *
            ∑ a : α, _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (A a) (B a) := by
              simp [_root_.LIDT.MIPStarRE.LDT.avgOver, _root_.LIDT.MIPStarRE.LDT.uniformDistribution, Finset.mul_sum]
      _ = (1 / (Fintype.card β : _root_.LIDT.MIPStarRE.LDT.Error)) *
            ∑ a : α, _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (A a) (B a) := by
              rw [Fintype.card_congr e]
      _ = (1 / (Fintype.card β : _root_.LIDT.MIPStarRE.LDT.Error)) *
            ∑ b : β, _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (A (e.symm b)) (B (e.symm b)) := by
              congr 1
              exact (Fintype.sum_equiv e
                (fun a => _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (A a) (B a))
                (fun b => _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (A (e.symm b)) (B (e.symm b)))
                (by intro a; simp))
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β)
            (fun b => _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (A (e.symm b)) (B (e.symm b))) := by
              simp [_root_.LIDT.MIPStarRE.LDT.avgOver, _root_.LIDT.MIPStarRE.LDT.uniformDistribution, Finset.mul_sum]
  constructor <;> rintro ⟨h⟩ <;> constructor <;> simpa [hEq] using h
