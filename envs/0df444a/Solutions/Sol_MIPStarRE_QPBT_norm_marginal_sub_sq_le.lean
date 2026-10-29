-- Prove2me | solution 1 for MIPStarRE.QPBT.norm_marginal_sub_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:57:06.165096+00:00
-- url     : https://prove2.me/submissions/f4e6407a-fa8b-481c-ae54-eca99e53cfe2

-- Generated proof for MIPStarRE.QPBT.norm_marginal_sub_sq_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_norm_finset_sum_projector_mul_sq_le
import Theorems.Thm_MIPStarRE_QPBT_norm_sub_projective_mul_sq_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Marginal contraction for combined point measurements

This module records a formalization-only auxiliary estimate for recovering a
marginal operator from a projective refinement. It combines the two contraction
steps in the combined-line argument into a pointwise factor-four bound.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:902-927`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

theorem solution {β ι : Type*} [Fintype β]
    [Fintype ι] [DecidableEq ι] (Q : β → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (hQ : ∀ b, _root_.LIDT.MIPStarRE.Quantum.IsProj (Q b))
    (horth : ∀ {b c}, b ≠ c → Q b * Q c = 0)
    (B : _root_.LIDT.MIPStarRE.Quantum.Measurement β ι) (hB : _root_.MIPStarRE.QPBT.Measurement.IsProjective B)
    (hcomm : ∀ b, Q b * B.effect b = B.effect b * Q b)
    (D : _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState ((∑ b, Q b) - D) ψ‖ ^ 2 ≤
      4 * ∑ b, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (Q b - B.effect b * D) ψ‖ ^ 2 := by
  classical
  let U : _root_.LIDT.MIPStarRE.Quantum.Op ι := ∑ b, Q b * (Q b - B.effect b * Q b)
  let V : _root_.LIDT.MIPStarRE.Quantum.Op ι := ∑ b, B.effect b * (Q b - B.effect b * D)
  have hU : ‖_root_.MIPStarRE.QPBT.applyOperatorToState U ψ‖ ^ 2 ≤
      ∑ b, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (Q b - B.effect b * D) ψ‖ ^ 2 := by
    refine le_trans (_root_.MIPStarRE.QPBT.DistanceCalculus.norm_finset_sum_projector_mul_sq_le
      Q (fun b => Q b - B.effect b * Q b) hQ horth Finset.univ ψ) ?_
    exact Finset.sum_le_sum fun b _ => _root_.MIPStarRE.QPBT.norm_sub_projective_mul_sq_le B hB b (Q b) D ψ
  have hV : ‖_root_.MIPStarRE.QPBT.applyOperatorToState V ψ‖ ^ 2 ≤
      ∑ b, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (Q b - B.effect b * D) ψ‖ ^ 2 :=
    _root_.MIPStarRE.QPBT.DistanceCalculus.norm_finset_sum_projector_mul_sq_le B.effect
      (fun b => Q b - B.effect b * D) hB
      (fun hbc => _root_.MIPStarRE.QPBT.DistanceCalculus.projective_effect_mul_effect_eq_zero B hB hbc)
      Finset.univ ψ
  have hsum : (∑ b, Q b) - D = U + V := by
    have hfirst : U = ∑ b, (Q b - B.effect b * Q b) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [mul_sub, ← mul_assoc, hcomm b, mul_assoc,
        (hQ b).isIdempotentElem.eq]
    have hsecond : V = (∑ b, B.effect b * Q b) - D := by
      dsimp [V]
      simp only [mul_sub, ← mul_assoc, (hB _).isIdempotentElem.eq,
        Finset.sum_sub_distrib, ← Finset.sum_mul, B.sum_eq_one, one_mul]
    rw [hfirst, hsecond, Finset.sum_sub_distrib]
    abel
  rw [hsum]
  have htriangle : ‖_root_.MIPStarRE.QPBT.applyOperatorToState (U + V) ψ‖ ≤
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState U ψ‖ + ‖_root_.MIPStarRE.QPBT.applyOperatorToState V ψ‖ := by
    simpa only [_root_.MIPStarRE.QPBT.applyOperatorToState, map_add, LinearMap.add_apply] using
      norm_add_le (_root_.MIPStarRE.QPBT.applyOperatorToState U ψ) (_root_.MIPStarRE.QPBT.applyOperatorToState V ψ)
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  nlinarith [sq_nonneg (‖_root_.MIPStarRE.QPBT.applyOperatorToState U ψ‖ - ‖_root_.MIPStarRE.QPBT.applyOperatorToState V ψ‖)]
