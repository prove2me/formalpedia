-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.gBotSelfConsistency_ofCompleteSelfConsistency
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:44:31.386866+00:00
-- url     : https://prove2.me/submissions/0dde232a-b207-4e0c-9195-0d86b399b8f4

-- Generated proof for MIPStarRE.LDT.Pasting.gBotSelfConsistency_ofCompleteSelfConsistency.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_qSDD_completePart_le_slice

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Section 12 pasting: complete and incomplete part self-consistency

Scalar and state-dependent-distance consequences for the complete and incomplete
parts of the pasted slice family.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (_hperm : _root_.LIDT.MIPStarRE.LDT.PermInvState ψbi)
    (hcomplete : _root_.LIDT.MIPStarRE.LDT.Pasting.GCompleteSelfConsistencyStatement params ψbi family zeta) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.GBotSelfConsistencyStatement params ψbi family zeta := by
  refine {
    incompletePartSelfConsistency := ?_
  }
  rcases hcomplete.completePartSelfConsistency with ⟨hcomplete_bound⟩
  have hcomplete_total :
      _root_.LIDT.MIPStarRE.LDT.sddError ψbi
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
          (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartLeftFamily params family)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartRightFamily params family)
        ≤ zeta := by
    unfold _root_.LIDT.MIPStarRE.LDT.sddError at *
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
          (fun x =>
            _root_.LIDT.MIPStarRE.LDT.qSDD ψbi
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartLeftFamily params family) x)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartRightFamily params family) x))
        ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
            (fun x =>
              _root_.LIDT.MIPStarRE.LDT.qSDD ψbi
                ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas family.meas)) x)
                ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas family.meas)) x)) := by
              apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
              intro x
              simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.completePartLeftFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartRightFamily,
                _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft, _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight, _root_.LIDT.MIPStarRE.LDT.SubMeas.liftLeft,
                _root_.LIDT.MIPStarRE.LDT.SubMeas.liftRight, _root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas, _root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas,
                _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas] using
                _root_.LIDT.MIPStarRE.LDT.Pasting.qSDD_completePart_le_slice params ψbi family x
      _ ≤ zeta := hcomplete_bound
  refine ⟨?_⟩
  calc
    _root_.LIDT.MIPStarRE.LDT.sddError ψbi
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
        (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartLeftFamily params family)
        (_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartRightFamily params family)
      =
        _root_.LIDT.MIPStarRE.LDT.sddError ψbi
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SliceQuestion params))
          (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartLeftFamily params family)
          (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartRightFamily params family) := by
            unfold _root_.LIDT.MIPStarRE.LDT.sddError
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            intro x
            unfold _root_.LIDT.MIPStarRE.LDT.qSDD _root_.LIDT.MIPStarRE.LDT.qSDDCore
            let T : _root_.LIDT.MIPStarRE.Quantum.Op ι := (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family x).total
            have hdiff :
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (1 - T) - _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - T) =
                  - (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T - _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T) := by
              ext i j
              rcases i with ⟨i₁, i₂⟩
              rcases j with ⟨j₁, j₂⟩
              simp [T, _root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.rightTensor, sub_eq_add_neg]
              ring
            calc
              _root_.LIDT.MIPStarRE.LDT.qSDD ψbi
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartLeftFamily params family) x)
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartRightFamily params family) x)
                =
                  _root_.LIDT.MIPStarRE.LDT.ev ψbi
                    (((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (1 - T) -
                        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - T))ᴴ) *
                      (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (1 - T) -
                        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - T))) := by
                          simp [_root_.LIDT.MIPStarRE.LDT.qSDD, _root_.LIDT.MIPStarRE.LDT.qSDDCore, _root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartLeftFamily,
                            _root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartRightFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.incompletePartSubMeas,
                            _root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas, _root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas, T]
              _ =
                  _root_.LIDT.MIPStarRE.LDT.ev ψbi
                    ((-(_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T - _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T))ᴴ *
                      (-(_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T - _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T))) := by
                          rw [hdiff]
              _ =
                  _root_.LIDT.MIPStarRE.LDT.ev ψbi
                    (((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T - _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T)ᴴ) *
                      (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T - _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T)) := by
                          have hswap :
                              ((_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T)ᴴ -
                                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T)ᴴ) *
                                  (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T - _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T) =
                                ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T)ᴴ -
                                    (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T)ᴴ) *
                                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) T - _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) T) := by
                            noncomm_ring
                          simpa [sub_eq_add_neg] using congrArg (_root_.LIDT.MIPStarRE.LDT.ev ψbi) hswap
              _ =
                  _root_.LIDT.MIPStarRE.LDT.qSDD ψbi
                    ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartLeftFamily params family) x)
                    ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartRightFamily params family) x) := by
                          simp [_root_.LIDT.MIPStarRE.LDT.qSDD, _root_.LIDT.MIPStarRE.LDT.qSDDCore, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartLeftFamily,
                            _root_.LIDT.MIPStarRE.LDT.Pasting.completePartRightFamily, _root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas,
                            _root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas, _root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas, T,
                            (family.meas x).sum_eq_total]
    _ ≤ zeta := hcomplete_total
