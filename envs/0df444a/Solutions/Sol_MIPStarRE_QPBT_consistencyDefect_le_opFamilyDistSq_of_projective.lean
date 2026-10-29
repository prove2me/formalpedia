-- Prove2me | solution 1 for MIPStarRE.QPBT.consistencyDefect_le_opFamilyDistSq_of_projective
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:06:37.278021+00:00
-- url     : https://prove2.me/submissions/70e087fe-4518-4213-93a5-0b5628c7b1c8

-- Generated proof for MIPStarRE.QPBT.consistencyDefect_le_opFamilyDistSq_of_projective.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_point_distance_eq_two_defect_of_projective

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

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective























































/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): the matrix-vector term in `consistencyDefect` is the state quadratic
form. -/
theorem consistency_term_eq_stateQForm {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (inner ℂ ψ ((EuclideanSpace.equiv ι ℂ).symm (M.mulVec ψ))).re =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  rfl





/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14), item 2: state-dependent squared distance between operator families is
nonnegative. -/
theorem opFamilyDistSq_nonneg {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (M N : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    0 ≤ _root_.MIPStarRE.QPBT.opFamilyDistSq μ M N ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq _root_.LIDT.MIPStarRE.LDT.avgOver
  exact Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonnegative x)
    (Finset.sum_nonneg fun a _ => sq_nonneg _)





























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
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι)
    (hA : ∀ x, _root_.MIPStarRE.QPBT.Measurement.IsProjective (A x))
    (hB : ∀ x, _root_.MIPStarRE.QPBT.Measurement.IsProjective (B x)) :
    _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ ≤
      _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ := by
  have heq :
      _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => (A x).effect a)
          (fun x a => (B x).effect a) ψ =
        2 * _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => (A x).effect a)
          (fun x a => (B x).effect a) ψ := by
    unfold _root_.MIPStarRE.QPBT.opFamilyDistSq _root_.MIPStarRE.QPBT.consistencyDefect _root_.LIDT.MIPStarRE.LDT.avgOver
    simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm]
    calc
      (∑ x ∈ μ.support, μ.weight x *
          ∑ a : α,
            ‖_root_.MIPStarRE.QPBT.applyOperatorToState ((A x).effect a - (B x).effect a) ψ‖ ^ 2) =
        ∑ x ∈ μ.support, μ.weight x *
          (2 * ∑ a : α, ∑ b : α, if a = b then 0 else
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (B x).effect b)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [_root_.MIPStarRE.QPBT.DistanceCalculus.point_distance_eq_two_defect_of_projective
          (A x) (B x) ψ (hA x) (hB x)]
      _ = 2 * ∑ x ∈ μ.support, μ.weight x *
          (∑ a : α, ∑ b : α, if a = b then 0 else
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (B x).effect b)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
  have hnonneg := _root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_nonneg μ
    (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ
  nlinarith
