-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Preliminaries.otherTwoNotionsOfSelfConsistency
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:19:23.027533+00:00
-- url     : https://prove2.me/submissions/b5828184-8426-49e4-badd-18273cfcfc08

-- Generated proof for MIPStarRE.LDT.Preliminaries.otherTwoNotionsOfSelfConsistency.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
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
# Self-consistency: core squared-mass bounds

Squared-mass lower bound lemma derived from bipartite self-consistency on
permutation-invariant states (`prop:cool-prop`).

## References

- `references/ldt-paper/preliminaries.tex`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

theorem solution {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (A : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas Question Outcome ι) (δ : _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.BipartiteSSCRel ψ 𝒟 A δ →
      @_root_.LIDT.MIPStarRE.LDT.ConsRel Question Outcome ι ι _ _ _ _ _ ψ 𝒟 A A δ := by
  intro ⟨hssc⟩
  constructor
  rw [_root_.LIDT.MIPStarRE.LDT.bipartiteConsError_eq_consError_placed]
  unfold _root_.LIDT.MIPStarRE.LDT.consError
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
        (fun q =>
          _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft A) q) ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight A) q))
      ≤ _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qBipartiteSSCDefect ψ (A q)) := by
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
          intro q
          let M := A q
          have htotal_le :
              _root_.LIDT.MIPStarRE.LDT.ev ψ (M.liftLeft.total * M.liftRight.total) ≤
                _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) M.total) := by
            have hopTensor_le :
                _root_.LIDT.MIPStarRE.LDT.opTensor M.total M.total ≤ _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) M.total := by
              have hrewrite :
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) M.total - _root_.LIDT.MIPStarRE.LDT.opTensor M.total M.total =
                    _root_.LIDT.MIPStarRE.LDT.opTensor M.total (1 - M.total) := by
                have hneg :
                    Matrix.kronecker M.total (-M.total) =
                      -Matrix.kronecker M.total M.total := by
                  simpa using
                    (Matrix.kronecker_smul (-1 : ℂ) M.total M.total)
                calc
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) M.total - _root_.LIDT.MIPStarRE.LDT.opTensor M.total M.total
                    = Matrix.kronecker M.total 1 +
                        Matrix.kronecker M.total (-M.total) := by
                          rw [hneg]
                          simp [_root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor, sub_eq_add_neg]
                  _ = Matrix.kronecker M.total (1 - M.total) := by
                        simpa [sub_eq_add_neg] using
                          (Matrix.kronecker_add M.total 1 (-M.total)).symm
                  _ = _root_.LIDT.MIPStarRE.LDT.opTensor M.total (1 - M.total) := by
                        simp [_root_.LIDT.MIPStarRE.LDT.opTensor]
              change
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) M.total - _root_.LIDT.MIPStarRE.LDT.opTensor M.total M.total).PosSemidef
              rw [hrewrite]
              change Matrix.PosSemidef (Matrix.kronecker M.total (1 - M.total))
              exact
                Matrix.PosSemidef.kronecker
                  (Matrix.nonneg_iff_posSemidef.mp M.total_nonneg)
                  (Matrix.nonneg_iff_posSemidef.mp
                    (sub_nonneg.mpr M.total_le_one))
            have hmono :
                _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor M.total M.total) ≤
                  _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) M.total) :=
              _root_.LIDT.MIPStarRE.LDT.ev_mono ψ _ _ hopTensor_le
            simpa [_root_.LIDT.MIPStarRE.LDT.SubMeas.liftLeft, _root_.LIDT.MIPStarRE.LDT.SubMeas.liftRight,
              _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor] using hmono
          have hmatch :
              _root_.LIDT.MIPStarRE.LDT.qMatchMass ψ M.liftLeft M.liftRight =
                ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (M.outcome a) (M.outcome a)) := by
            simp [_root_.LIDT.MIPStarRE.LDT.qMatchMass, _root_.LIDT.MIPStarRE.LDT.SubMeas.liftLeft, _root_.LIDT.MIPStarRE.LDT.SubMeas.liftRight,
              _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
          have hinner :
              _root_.LIDT.MIPStarRE.LDT.ev ψ (M.liftLeft.total * M.liftRight.total) -
                  _root_.LIDT.MIPStarRE.LDT.qMatchMass ψ M.liftLeft M.liftRight ≤
                _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) M.total) -
                  ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (M.outcome a) (M.outcome a)) := by
            rw [hmatch]
            exact sub_le_sub_right htotal_le _
          change
            max 0
                (_root_.LIDT.MIPStarRE.LDT.ev ψ (M.liftLeft.total * M.liftRight.total) -
                  _root_.LIDT.MIPStarRE.LDT.qMatchMass ψ M.liftLeft M.liftRight)
              ≤
            max 0
                (_root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) M.total) -
                  ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (M.outcome a) (M.outcome a)))
          exact max_le_max le_rfl hinner
      _ ≤ δ := hssc
