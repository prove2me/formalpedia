-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.qSDD_rightPlaced_zeroProjSubMeas_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:14:57.285061+00:00
-- url     : https://prove2.me/submissions/6b1665e9-08d6-489e-b1b2-fba11f3ddf18

-- Generated proof for MIPStarRE.LDT.MakingMeasurementsProjective.qSDD_rightPlaced_zeroProjSubMeas_le_one.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
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
# Section 5 — Rounding To Projectors Core

Internal lemmas for the orthogonalization and rounding-to-projectors chain.

This file extracts the consistency-to-almost-projective and spectral/rounding
steps so that `QXPLayer.lean` can depend on them without importing the full
Section 5 theorem file.

## References

- `references/ldt-paper/orthonormalization.tex`
- `blueprint/src/chapter/ch04_projective.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-! ### Orthonormalization helper lemmas -/















/-
The consistency defect of `(A,B)` controls the strong self-consistency defect
of the left-placed version of `A`. The Cauchy–Schwarz chain and tensor
hermitian identities have been factored out above, so the main proof is now a
straightforward combination of those helpers.
-/

theorem solution {Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (A : _root_.LIDT.MIPStarRE.LDT.SubMeas Outcome ιB) :
    _root_.LIDT.MIPStarRE.LDT.qSDD ψ (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) A)
      (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA)
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zeroProjSubMeas (Outcome := Outcome) (ι := ιB)).toSubMeas) ≤ 1 := by
  have hq :
      _root_.LIDT.MIPStarRE.LDT.qSDD ψ (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) A)
          (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA)
            (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zeroProjSubMeas (Outcome := Outcome) (ι := ιB)).toSubMeas) =
        ∑ a : Outcome,
          _root_.LIDT.MIPStarRE.LDT.ev ψ (((_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) A).outcome a) *
            ((_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) A).outcome a)) := by
    unfold _root_.LIDT.MIPStarRE.LDT.qSDD _root_.LIDT.MIPStarRE.LDT.qSDDCore
    refine Finset.sum_congr rfl ?_
    intro a _
    let Z : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB) := (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) A).outcome a
    have hzero :
        (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA)
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zeroProjSubMeas (Outcome := Outcome) (ι := ιB)).toSubMeas).outcome a = 0 := by
      ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
        simp [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zeroProjSubMeas, _root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas, _root_.LIDT.MIPStarRE.LDT.rightTensor, h₁, h₂]
    calc
      _root_.LIDT.MIPStarRE.LDT.ev ψ
          ((Z -
              (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA)
                (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zeroProjSubMeas (Outcome := Outcome) (ι := ιB)).toSubMeas).outcome a)ᴴ *
            (Z - (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA)
              (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zeroProjSubMeas (Outcome := Outcome) (ι := ιB)).toSubMeas).outcome a))
        = _root_.LIDT.MIPStarRE.LDT.ev ψ (Zᴴ * Z) := by
            rw [hzero]
            simp
      _ = _root_.LIDT.MIPStarRE.LDT.ev ψ (Z * Z) := by
            rw [_root_.LIDT.MIPStarRE.LDT.SubMeas.outcome_hermitian (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) A) a]
      _ = _root_.LIDT.MIPStarRE.LDT.ev ψ (((_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) A).outcome a) *
            ((_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) A).outcome a)) := by
            rfl
  rw [hq]
  simpa using
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_one ψ hψ
      (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) A)
