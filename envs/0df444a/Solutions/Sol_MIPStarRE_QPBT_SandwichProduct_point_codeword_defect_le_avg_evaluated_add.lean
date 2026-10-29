-- Prove2me | solution 1 for MIPStarRE.QPBT.SandwichProduct.point_codeword_defect_le_avg_evaluated_add
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:52:45.179557+00:00
-- url     : https://prove2.me/submissions/30f68f46-0eff-467c-a6ed-871561030ef5

-- Generated proof for MIPStarRE.QPBT.SandwichProduct.point_codeword_defect_le_avg_evaluated_add.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_point_defect_eq
import Theorems.Thm_MIPStarRE_QPBT_SandwichProduct_avg_diagonal_postprocess_stateQForm_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.SandwichProduct
end MIPStarRE.QPBT.SandwichProduct

/- Source helpers from QPBT/Games/DistanceTheorems/TensorSupport.lean. -/
/-!
# Tensor-placement and marginal identities

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- Blueprint `fact:triangle-for-simeq`, `fact:data-processing`, and
  `lem:commutation-analysis`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective





/-- Formalization-only auxiliary lemma for Fact 4.26: products of left and right
placements evaluate as a Kronecker product. -/
theorem placed_product_stateQForm_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A 1 * _root_.MIPStarRE.QPBT.heteroKron 1 B) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A B) := by
  congr 1
  exact _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor A B































end MIPStarRE.QPBT.DistanceCalculus

/-! # Quantitative support for sandwiched measurements

This module develops the consistency and operator-distance estimates used
in the quantitative sandwich argument.

## References

Blueprint `lem:ld-sandwich` and `lem:ld-sandwich-measurement`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus

open MIPStarRE.QPBT.SandwichProduct

set_option maxHeartbeats 600000 in
-- Complementary overlaps require simultaneous expansions before averaging.

theorem solution
    {Y Γ R ιA ιB : Type*}
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Γ] [DecidableEq Γ] [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : _root_.LIDT.MIPStarRE.Quantum.Measurement Γ ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (eval : Γ → Y → R) (ε : ℝ)
    (hψ : ‖ψ‖ = 1) (hε : 0 ≤ ε)
    (hcollision : ∀ g g' : Γ, g ≠ g' →
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y)
        (fun y => if eval g y = eval g' y then 1 else 0) ≤ ε) :
    (∑ g : Γ, ∑ g' : Γ, if g = g' then 0 else
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (A.effect g) (B.effect g'))) ≤
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (fun y =>
        ∑ r : R, ∑ r' : R, if r = r' then 0 else
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
            (_root_.MIPStarRE.QPBT.heteroKron
              ((A.postprocess (fun g => eval g y)).effect r)
              ((B.postprocess (fun g => eval g y)).effect r'))) + ε := by
  have hdiag_avg := _root_.MIPStarRE.QPBT.SandwichProduct.avg_diagonal_postprocess_stateQForm_le
    A B ψ eval ε hψ hε hcollision
  have hfull := _root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq
    (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ιB) A)
    (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := ιA) B) ψ
  simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement, _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement,
    _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] at hfull
  simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq] at hfull
  have hevaluated (y : Y) := _root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq
    (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ιB)
      (A.postprocess (fun g => eval g y)))
    (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := ιA)
      (B.postprocess (fun g => eval g y))) ψ
  simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement, _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement,
    _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] at hevaluated
  simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq] at hevaluated
  have heval_avg : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (fun y =>
      ∑ r : R, ∑ r' : R, if r = r' then 0 else
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
          (_root_.MIPStarRE.QPBT.heteroKron
            ((A.postprocess (fun g => eval g y)).effect r)
            ((B.postprocess (fun g => eval g y)).effect r'))) =
      1 - _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (fun y =>
        ∑ r : R, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
          (_root_.MIPStarRE.QPBT.heteroKron
            ((A.postprocess (fun g => eval g y)).effect r)
            ((B.postprocess (fun g => eval g y)).effect r))) := by
    simp_rw [hevaluated]
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const]
    rw [hψ]
    norm_num
  rw [hfull, hψ, one_pow, heval_avg]
  linarith
