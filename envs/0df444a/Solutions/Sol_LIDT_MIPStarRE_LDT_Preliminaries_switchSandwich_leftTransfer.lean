-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Preliminaries.switchSandwich_leftTransfer
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:30:45.880323+00:00
-- url     : https://prove2.me/submissions/ee0a626e-3ef7-46f0-aeab-2b915c5c9a41

-- Generated proof for MIPStarRE.LDT.Preliminaries.switchSandwich_leftTransfer.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_question_switchSandwich_left_gap
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_question_switchSandwich_middle_gap

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Switch-sandwich main: left-to-middle transfer

The left-to-middle transfer estimate used in `prop:switch-sandwich`, bounding
the gap between the left and middle expressions via the Cauchy–Schwarz-based
gap bounds.

## References

- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

theorem solution
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι)) (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas Question Outcome ι)
    (B : _root_.LIDT.MIPStarRE.Quantum.Op ι) (hB : _root_.LIDT.MIPStarRE.LDT.Preliminaries.OpBounded01 B)
    (δ : _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.BipartiteSDDRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas A)
      (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas A) δ →
    |_root_.LIDT.MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψ 𝒟 A B -
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψ 𝒟 A B| ≤
      2 * Real.sqrt δ := by
  intro happrox
  let inter : _root_.LIDT.MIPStarRE.LDT.Error :=
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 fun q =>
      ∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))
  have hδ :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
        (fun q =>
          _root_.LIDT.MIPStarRE.LDT.qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight)) ≤ δ := by
    simpa [_root_.LIDT.MIPStarRE.LDT.Preliminaries.BipartiteSDDRel, _root_.LIDT.MIPStarRE.LDT.sddError, _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas, _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft,
      _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight, _root_.LIDT.MIPStarRE.LDT.SubMeas.liftLeft, _root_.LIDT.MIPStarRE.LDT.SubMeas.liftRight] using
      happrox.leftRightSquaredDistanceBound
  have hleft_gap :
      |_root_.LIDT.MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψ 𝒟 A B - inter| ≤ Real.sqrt δ := by
    calc
      |_root_.LIDT.MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψ 𝒟 A B - inter|
        = |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q =>
            (∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a))) -
            ∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a)))| := by
              simp [_root_.LIDT.MIPStarRE.LDT.Preliminaries.leftSandwichExpectation, inter, _root_.LIDT.MIPStarRE.LDT.avgOver, Finset.sum_sub_distrib, mul_sub]
      _ ≤
          Real.sqrt
            (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
              (fun q =>
                _root_.LIDT.MIPStarRE.LDT.qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))) := by
            exact
              _root_.LIDT.MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise 𝒟
                (fun q =>
                  (∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
                      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a))) -
                  ∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
                      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a)))
                (fun q =>
                  _root_.LIDT.MIPStarRE.LDT.qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
                (fun q => by
                  simpa using
                    _root_.LIDT.MIPStarRE.LDT.Preliminaries.question_switchSandwich_left_gap ψ hψ (A q) B hB)
                (fun q => _root_.LIDT.MIPStarRE.LDT.qSDD_nonneg ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
                h𝒟
      _ ≤ Real.sqrt δ := by
            exact Real.sqrt_le_sqrt hδ
  have hmiddle_gap :
      |inter - _root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψ 𝒟 A B| ≤ Real.sqrt δ := by
    calc
      |inter - _root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψ 𝒟 A B|
        = |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q =>
            (∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))) -
            ∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a)))| := by
              simp [_root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation, inter, _root_.LIDT.MIPStarRE.LDT.avgOver, Finset.sum_sub_distrib, mul_sub]
      _ ≤
          Real.sqrt
            (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
              (fun q =>
                _root_.LIDT.MIPStarRE.LDT.qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))) := by
            exact
              _root_.LIDT.MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise 𝒟
                (fun q =>
                  (∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
                      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))) -
                  ∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a)))
                (fun q =>
                  _root_.LIDT.MIPStarRE.LDT.qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
                (fun q => by
                  simpa using
                    _root_.LIDT.MIPStarRE.LDT.Preliminaries.question_switchSandwich_middle_gap ψ hψ (A q) B hB)
                (fun q => _root_.LIDT.MIPStarRE.LDT.qSDD_nonneg ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
                h𝒟
      _ ≤ Real.sqrt δ := by
            exact Real.sqrt_le_sqrt hδ
  calc
    |_root_.LIDT.MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψ 𝒟 A B - _root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψ 𝒟 A B|
      ≤
        |_root_.LIDT.MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψ 𝒟 A B - inter| +
          |inter - _root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψ 𝒟 A B| := by
            exact
              abs_sub_le
                (_root_.LIDT.MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψ 𝒟 A B)
                inter
                (_root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψ 𝒟 A B)
    _ ≤ Real.sqrt δ + Real.sqrt δ := add_le_add hleft_gap hmiddle_gap
    _ = 2 * Real.sqrt δ := by ring
