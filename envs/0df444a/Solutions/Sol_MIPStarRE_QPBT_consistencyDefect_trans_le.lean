-- Prove2me | solution 1 for MIPStarRE.QPBT.consistencyDefect_trans_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:10:09.324536+00:00
-- url     : https://prove2.me/submissions/22b5a492-e38c-45be-bea4-382d00c9e609

-- Generated proof for MIPStarRE.QPBT.consistencyDefect_trans_le.
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
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_consistencyDefect_eq_one_sub_overlap
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_overlap_gap_le_of_opFamilyDistSq
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_le_of_le_of_le
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_le_two_mul_consistencyDefect

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

























































































/-- Formalization-only auxiliary lemma for Proposition 4.29: state-dependent
operator-family distance is symmetric. -/
theorem opFamilyDistSq_symm {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ B A ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  simp only [_root_.MIPStarRE.QPBT.applyOperatorToState, map_sub, LinearMap.sub_apply]
  rw [norm_sub_rev]

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
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B C D : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (ε δ γ : ℝ)
    (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (hAB : _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => (A x).effect a)
      (fun x a => (B x).effect a) ψ ≤ ε)
    (hCB : _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => (C x).effect a)
      (fun x a => (B x).effect a) ψ ≤ δ)
    (hCD : _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => (C x).effect a)
      (fun x a => (D x).effect a) ψ ≤ γ) :
    _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => (A x).effect a)
      (fun x a => (D x).effect a) ψ ≤ ε + 2 * Real.sqrt (δ + γ) := by
  letI : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    letI := hι
    have hzero : ψ = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero] at hψ
    norm_num at hψ
  have hCBdist : _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => (C x).effect a)
      (fun x a => (B x).effect a) ψ ≤ 2 * δ := by
    calc
      _ ≤ 2 * _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => (C x).effect a)
          (fun x a => (B x).effect a) ψ :=
        _root_.MIPStarRE.QPBT.opFamilyDistSq_le_two_mul_consistencyDefect μ C B ψ
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hCB (by norm_num)
  have hBCdist : _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => (B x).effect a)
      (fun x a => (C x).effect a) ψ ≤ 2 * δ := by
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_symm]
    exact hCBdist
  have hCDdist : _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => (C x).effect a)
      (fun x a => (D x).effect a) ψ ≤ 2 * γ := by
    calc
      _ ≤ 2 * _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => (C x).effect a)
          (fun x a => (D x).effect a) ψ :=
        _root_.MIPStarRE.QPBT.opFamilyDistSq_le_two_mul_consistencyDefect μ C D ψ
      _ ≤ 2 * γ := mul_le_mul_of_nonneg_left hCD (by norm_num)
  have hBDdist : _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => (B x).effect a)
      (fun x a => (D x).effect a) ψ ≤ 4 * (δ + γ) := by
    have htri := _root_.MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le μ
      (fun x a => (B x).effect a) (fun x a => (C x).effect a)
      (fun x a => (D x).effect a) ψ (2 * δ) (2 * γ) hBCdist hCDdist
    linarith
  have hgap := _root_.MIPStarRE.QPBT.DistanceCalculus.overlap_gap_le_of_opFamilyDistSq μ A B D ψ hμ hψ
    (4 * (δ + γ)) hBDdist
  have hsqrt : Real.sqrt (4 * (δ + γ)) = 2 * Real.sqrt (δ + γ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ A B ψ hμ hψ] at hAB
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ A D ψ hμ hψ]
  have hdiff :
      _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (B x).effect a)) -
        _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (D x).effect a)) ≤
        2 * Real.sqrt (δ + γ) := by
    calc
      _ ≤ |avgOver μ (fun x => ∑ a,
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (B x).effect a)) -
          _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (D x).effect a))| := le_abs_self _
      _ ≤ Real.sqrt (4 * (δ + γ)) := hgap
      _ = 2 * Real.sqrt (δ + γ) := hsqrt
  linarith
