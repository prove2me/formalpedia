-- Prove2me | solution 1 for MIPStarRE.QPBT.avg_closeness
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:32:14.291992+00:00
-- url     : https://prove2.me/submissions/aeec4c52-0f6c-4e6b-a221-057cceac17e7

-- Generated proof for MIPStarRE.QPBT.avg_closeness.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_QPBT_QPBT_Games_Consistency
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

/-! # State-dependent distance calculus

This module records the consistency and state-dependent distance estimates used
throughout the quantum Pauli basis test. The statements retain explicit
constants that the paper absorbs into asymptotic notation.

The operator-level inequalities they rest on live in
`MIPStarRE.QPBT.Games.DistanceTheorems.Calculus`.

## References

The source results run from blueprint `fact:agreement` through
`lem:close-strategies-have-close-values`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-461` and
`:531-540`. The observable conversion lemmas come from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:95-131`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem solution {X ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (hμ : μ.IsProbability) (A B : X → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (α : X → ℂ) (hα : ∀ x, ‖α x‖ ≤ 1) (ψ : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution μ fun x =>
          α x • (A x - B x)) ψ‖ ^ 2 ≤
      _root_.MIPStarRE.QPBT.opDistSq μ A B ψ := by
  let v : X → EuclideanSpace ℂ ι :=
    fun x => _root_.MIPStarRE.QPBT.applyOperatorToState (A x - B x) ψ
  have happly :
      _root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution μ fun x => α x • (A x - B x)) ψ =
        ∑ x ∈ μ.support, μ.weight x • (α x • v x) := by
    unfold _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution _root_.MIPStarRE.QPBT.applyOperatorToState
    rw [map_sum]
    simp only [LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro x _
    rw [← smul_assoc, map_smul]
    simp only [v, _root_.MIPStarRE.QPBT.applyOperatorToState, Complex.real_smul, map_sub,
      LinearMap.smul_apply, LinearMap.sub_apply]
    rw [← smul_assoc, Complex.real_smul]
  have hnorm :
      ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ≤
        ∑ x ∈ μ.support, μ.weight x * ‖v x‖ := by
    calc
      ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ≤
          ∑ x ∈ μ.support, ‖μ.weight x • (α x • v x)‖ :=
        norm_sum_le μ.support _
      _ ≤ ∑ x ∈ μ.support, μ.weight x * ‖v x‖ := by
        apply Finset.sum_le_sum
        intro x _
        rw [norm_smul_of_nonneg (μ.nonnegative x), norm_smul]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [one_mul] using
            mul_le_of_le_one_left (norm_nonneg (v x)) (hα x))
          (μ.nonnegative x)
  have hrhs_nonneg :
      0 ≤ ∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonnegative x) (sq_nonneg _)
  have havg_norm :
      |avgOver μ (fun x => ‖v x‖)| ≤
        Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ‖v x‖ ^ 2)) := by
    exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise μ
      (fun x => ‖v x‖) (fun x => ‖v x‖ ^ 2)
      (fun x => by rw [abs_norm, Real.sqrt_sq_eq_abs, abs_norm])
      (fun x => sq_nonneg ‖v x‖) (by rw [hμ.weight_sum_eq_one])
  have hnorm_sqrt :
      ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ≤
        Real.sqrt (∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2) := by
    calc
      ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ≤
          ∑ x ∈ μ.support, μ.weight x * ‖v x‖ := hnorm
      _ ≤ |avgOver μ (fun x => ‖v x‖)| := le_abs_self _
      _ ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ‖v x‖ ^ 2)) := havg_norm
  rw [happly]
  unfold _root_.MIPStarRE.QPBT.opDistSq _root_.MIPStarRE.QPBT.opFamilyDistSq _root_.LIDT.MIPStarRE.LDT.avgOver
  simp only [Fintype.sum_unique]
  change ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ^ 2 ≤
    ∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2
  calc
    ‖∑ x ∈ μ.support, μ.weight x • (α x • v x)‖ ^ 2 ≤
        (Real.sqrt (∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 hnorm_sqrt
    _ = ∑ x ∈ μ.support, μ.weight x * ‖v x‖ ^ 2 :=
      Real.sq_sqrt hrhs_nonneg
