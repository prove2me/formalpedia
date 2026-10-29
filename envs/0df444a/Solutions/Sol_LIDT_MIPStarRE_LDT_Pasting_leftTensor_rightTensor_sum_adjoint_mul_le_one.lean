-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.leftTensor_rightTensor_sum_adjoint_mul_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:12:51.443406+00:00
-- url     : https://prove2.me/submissions/e7d40f8b-865a-4064-a240-4f99a51bd321

-- Generated proof for MIPStarRE.LDT.Pasting.leftTensor_rightTensor_sum_adjoint_mul_le_one.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
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
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Section 12 pasting: commute G half-sandwich setup — sum bounds

Sum-of-adjoint-products `≤ 1` bounds for the half-product, reverse-half-product,
pair-prefix, and bipartite tensor families. Also contains the error-envelope bound
`commuteGHalfSandwich_error_bound` and its helper `rpow_oneSixteenth_nonneg`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Half-product sum bounds -/





/-! ### Error-envelope bound -/






/-! ### Pair-prefix and bipartite tensor bounds -/

theorem solution
    {α β : Type*}
    [Fintype α]
    [Fintype β]
    (prefixOp : α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (tailOp : β → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (hprefix : ∑ a : α, (prefixOp a)ᴴ * prefixOp a ≤ 1)
    (htail : ∑ b : β, (tailOp b)ᴴ * tailOp b ≤ 1) :
    ∑ ag : α × β,
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (prefixOp ag.1) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (tailOp ag.2))ᴴ *
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (prefixOp ag.1) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (tailOp ag.2)) ≤ 1 := by
  classical
  let prefixTerm : α → _root_.LIDT.MIPStarRE.Quantum.Op ι :=
    fun a => (prefixOp a)ᴴ * prefixOp a
  let tailTerm : β → _root_.LIDT.MIPStarRE.Quantum.Op ι :=
    fun b => (tailOp b)ᴴ * tailOp b
  calc
    ∑ ag : α × β,
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (prefixOp ag.1) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (tailOp ag.2))ᴴ *
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (prefixOp ag.1) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (tailOp ag.2))
      = ∑ a : α, ∑ b : β,
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (prefixTerm a) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (tailTerm b) := by
              rw [← Finset.univ_product_univ, Finset.sum_product]
              refine Finset.sum_congr rfl ?_
              intro a _
              refine Finset.sum_congr rfl ?_
              intro b _
              have hmul :
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (prefixOp a) *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (tailOp b) =
                    _root_.LIDT.MIPStarRE.LDT.opTensor (prefixOp a) (tailOp b) := by
                rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
              calc
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (prefixOp a) *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (tailOp b))ᴴ *
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (prefixOp a) *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (tailOp b))
                  = (_root_.LIDT.MIPStarRE.LDT.opTensor (prefixOp a) (tailOp b))ᴴ *
                      _root_.LIDT.MIPStarRE.LDT.opTensor (prefixOp a) (tailOp b) := by
                        rw [hmul]
                _ = _root_.LIDT.MIPStarRE.LDT.opTensor ((prefixOp a)ᴴ) ((tailOp b)ᴴ) *
                      _root_.LIDT.MIPStarRE.LDT.opTensor (prefixOp a) (tailOp b) := by
                        rw [_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor]
                _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (prefixTerm a) *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (tailTerm b) := by
                        simp [prefixTerm, tailTerm, _root_.LIDT.MIPStarRE.LDT.opTensor_mul]
    _ = ∑ a : α,
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (prefixTerm a) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (∑ b : β, tailTerm b) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [← _root_.LIDT.MIPStarRE.LDT.rightTensor_finset_sum (ι₁ := ι) Finset.univ tailTerm,
                ← Finset.mul_sum]
    _ ≤ ∑ a : α, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (prefixTerm a) := by
          refine Finset.sum_le_sum ?_
          intro a _
          have hprefix_nonneg : 0 ≤ prefixTerm a := by
            change 0 ≤ star (prefixOp a) * prefixOp a
            exact (CStarAlgebra.nonneg_iff_eq_star_mul_self).2 ⟨prefixOp a, rfl⟩
          calc
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (prefixTerm a) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (∑ b : β, tailTerm b)
              = _root_.LIDT.MIPStarRE.LDT.opTensor (prefixTerm a) (∑ b : β, tailTerm b) := by
                  rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
            _ ≤ _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (prefixTerm a) := by
                  exact _root_.LIDT.MIPStarRE.LDT.opTensor_le_leftTensor hprefix_nonneg htail
    _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (∑ a : α, prefixTerm a) := by
          rw [← _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ prefixTerm]
    _ ≤ 1 := by
          exact _root_.LIDT.MIPStarRE.LDT.leftTensor_le_one (ι₂ := ι) (A := _) hprefix
