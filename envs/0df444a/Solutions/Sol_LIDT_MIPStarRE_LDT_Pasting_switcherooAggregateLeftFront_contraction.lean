-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateLeftFront_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:03:35.767047+00:00
-- url     : https://prove2.me/submissions/b2cff890-9ce5-4249-a21c-ec8c13705275

-- Generated proof for MIPStarRE.LDT.Pasting.switcherooAggregateLeftFront_contraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_ScalarTerms
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_projSubMeas_sandwich_sum_le_one

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Section 12 pasting: switcheroo expansion

Expansion identities and the left-front contraction bound.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    {Outcome : Type*} [Fintype Outcome]
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (M : _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) Outcome ι)
    (q : _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params) :
    (∑ go : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
        (∑ _u : Unit,
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))ᴴ *
          (∑ _u : Unit,
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))) ≤ 1 := by
  calc
    (∑ go : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
        (∑ _u : Unit,
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))ᴴ *
          (∑ _u : Unit,
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2)))
      = ∑ go : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            ((M q.2).outcome go.2 *
              (family.meas q.1).outcome go.1 *
              (M q.2).outcome go.2) := by
            refine Finset.sum_congr rfl ?_
            intro go _
            calc
              (∑ _u : Unit,
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))ᴴ *
                (∑ _u : Unit,
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))
                = (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))ᴴ *
                    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2) := by
                        simp
              _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    ((((family.meas q.1).outcome go.1) * (M q.2).outcome go.2)ᴴ *
                      (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2)) := by
                        rw [show
                          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                              (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))ᴴ =
                            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                              ((((family.meas q.1).outcome go.1) * (M q.2).outcome go.2)ᴴ) by
                              simpa [_root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor] using
                                (_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor
                                  (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2)
                                  (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))]
                        rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor]
              _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    ((M q.2).outcome go.2 *
                      (family.meas q.1).outcome go.1 *
                      (M q.2).outcome go.2) := by
                        congr 1
                        have hGherm : ((family.meas q.1).outcome go.1)ᴴ =
                            (family.meas q.1).outcome go.1 :=
                          (family.meas q.1).outcome_hermitian go.1
                        have hMoherm : ((M q.2).outcome go.2)ᴴ =
                            (M q.2).outcome go.2 :=
                          (M q.2).outcome_hermitian go.2
                        calc
                          ((((family.meas q.1).outcome go.1) * (M q.2).outcome go.2)ᴴ) *
                              (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2)
                            = (((M q.2).outcome go.2) * (family.meas q.1).outcome go.1) *
                                (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2) := by
                                    simp [Matrix.conjTranspose_mul, hGherm, hMoherm]
                          _ = (M q.2).outcome go.2 *
                                ((family.meas q.1).outcome go.1 * (family.meas q.1).outcome go.1) *
                                (M q.2).outcome go.2 := by
                                    simp [mul_assoc]
                          _ = (M q.2).outcome go.2 *
                                (family.meas q.1).outcome go.1 *
                                (M q.2).outcome go.2 := by
                                    rw [(family.meas q.1).proj go.1]
    _ = ∑ o : Outcome,
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
            ((M q.2).outcome o * (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
              (M q.2).outcome o) := by
            calc
              ∑ go : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                    ((M q.2).outcome go.2 *
                      (family.meas q.1).outcome go.1 *
                      (M q.2).outcome go.2)
                = ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
                    ∑ o : Outcome,
                      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                        ((M q.2).outcome o *
                          (family.meas q.1).outcome g *
                          (M q.2).outcome o) := by
                          simpa using
                            (Fintype.sum_prod_type' (f := fun g o =>
                              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                                ((M q.2).outcome o *
                                  (family.meas q.1).outcome g *
                                  (M q.2).outcome o)))
              _ = ∑ o : Outcome,
                    ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
                      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                        ((M q.2).outcome o *
                          (family.meas q.1).outcome g *
                          (M q.2).outcome o) := by
                          rw [Finset.sum_comm]
              _ = ∑ o : Outcome,
                    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                      ((M q.2).outcome o * (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                        (M q.2).outcome o) := by
                          refine Finset.sum_congr rfl ?_
                          intro o _
                          rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ]
                          congr 1
                          calc
                            ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
                                (M q.2).outcome o * (family.meas q.1).outcome g * (M q.2).outcome o
                              = (M q.2).outcome o *
                                  (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, (family.meas q.1).outcome g) *
                                  (M q.2).outcome o := by
                                    simp [mul_assoc, Matrix.mul_sum, Finset.sum_mul]
                            _ = (M q.2).outcome o * (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                                  (M q.2).outcome o := by
                                    rw [(family.meas q.1).sum_eq_total]
                                    simp [_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas, _root_.LIDT.MIPStarRE.LDT.postprocess_total]
    _ ≤ 1 := by
          rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ]
          have hGle : (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total ≤ 1 :=
            (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total_le_one
          have hmid_le :
              ∑ o : Outcome,
                  (M q.2).outcome o * (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                    (M q.2).outcome o ≤ 1 := by
            exact _root_.LIDT.MIPStarRE.LDT.Pasting.projSubMeas_sandwich_sum_le_one (M q.2)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total) hGle
          calc
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                (∑ o : Outcome,
                  (M q.2).outcome o * (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                    (M q.2).outcome o)
              ≤ _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := by
                  simpa [_root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor] using
                    (_root_.LIDT.MIPStarRE.LDT.opTensor_mono_left (ι₂ := ι) (B := (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))
                      hmid_le (show (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ≤ 1 by exact zero_le_one))
            _ = 1 := by simp [_root_.LIDT.MIPStarRE.LDT.leftTensor]
