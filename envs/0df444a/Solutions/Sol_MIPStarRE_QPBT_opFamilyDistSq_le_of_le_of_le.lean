-- Prove2me | solution 1 for MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:40:56.968429+00:00
-- url     : https://prove2.me/submissions/c6827f08-e807-4ad1-9982-c261f2f01705

-- Generated proof for MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-!
# Consistency and state-dependent distance inequalities

This module collects the operator-level part of the state-dependent distance
calculus: the two-sided comparison between consistency defect and distance, the
monotonicity of the distance under products and function-indexed operators, its
triangle inequality and data-processing bound, and the approximate commutation
obtained from a joint projective refinement. The statements retain explicit
constants that the paper absorbs into asymptotic notation.

## References

The source results run from blueprint `fact:agreement` through
`lem:commutation-analysis`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-461`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem solution {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B C : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) (δ ε : ℝ)
    (hAB : _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ ≤ δ)
    (hBC : _root_.MIPStarRE.QPBT.opFamilyDistSq μ B C ψ ≤ ε) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ A C ψ ≤ 2 * δ + 2 * ε := by
  have hpoint : ∀ x a,
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x a - C x a) ψ‖ ^ 2 ≤
        2 * ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖ ^ 2 +
          2 * ‖_root_.MIPStarRE.QPBT.applyOperatorToState (B x a - C x a) ψ‖ ^ 2 := by
    intro x a
    have hdecomp : _root_.MIPStarRE.QPBT.applyOperatorToState (A x a - C x a) ψ =
        _root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ +
          _root_.MIPStarRE.QPBT.applyOperatorToState (B x a - C x a) ψ := by
      simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
    rw [hdecomp]
    let u := _root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ
    let v := _root_.MIPStarRE.QPBT.applyOperatorToState (B x a - C x a) ψ
    calc
      ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2
          (norm_add_le u v)
      _ ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
        nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq at *
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x a - C x a) ψ‖ ^ 2)
        ≤ _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
          (2 * ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖ ^ 2 +
            2 * ‖_root_.MIPStarRE.QPBT.applyOperatorToState (B x a - C x a) ψ‖ ^ 2)) := by
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
          intro x
          exact Finset.sum_le_sum fun a _ => hpoint x a
    _ = 2 * _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖ ^ 2) +
        2 * _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState (B x a - C x a) ψ‖ ^ 2) := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul, _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
    _ ≤ 2 * δ + 2 * ε := add_le_add
      (mul_le_mul_of_nonneg_left hAB (by positivity))
      (mul_le_mul_of_nonneg_left hBC (by positivity))
