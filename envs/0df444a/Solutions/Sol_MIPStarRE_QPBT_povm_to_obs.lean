-- Prove2me | solution 1 for MIPStarRE.QPBT.povm_to_obs
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:36:27.553117+00:00
-- url     : https://prove2.me/submissions/444ae6d9-e89e-449f-9560-f2655c96c442

-- Generated proof for MIPStarRE.QPBT.povm_to_obs.
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

theorem solution {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (c : α → ℂ) (hc : ∀ a, ‖c a‖ = 1) (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opDistSq μ (fun x => ∑ a, c a • A x a) (fun x => ∑ a, c a • B x a) ψ ≤
      Fintype.card α * _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ := by
  have hpoint : ∀ x,
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          ((∑ a, c a • A x a) - ∑ a, c a • B x a) ψ‖ ^ 2 ≤
        (Fintype.card α : ℝ) *
          ∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖ ^ 2 := by
    intro x
    have hrewrite :
        _root_.MIPStarRE.QPBT.applyOperatorToState
            ((∑ a, c a • A x a) - ∑ a, c a • B x a) ψ =
          ∑ a, c a • _root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ := by
      simp [_root_.MIPStarRE.QPBT.applyOperatorToState, ← Finset.sum_sub_distrib, ← smul_sub]
    rw [hrewrite]
    have hnorm :
        ‖∑ a, c a • _root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖ ≤
          ∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖ := by
      calc
        ‖∑ a, c a • _root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖ ≤
            ∑ a, ‖c a • _root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖ :=
          norm_sum_le Finset.univ _
        _ = ∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖ := by
          apply Finset.sum_congr rfl
          intro a _
          simp [norm_smul, hc a]
    calc
      ‖∑ a, c a • _root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖ ^ 2 ≤
          (∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 hnorm
      _ ≤ (Fintype.card α : ℝ) *
          ∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖ ^ 2 := by
        simpa using (sq_sum_le_card_mul_sum_sq
          (s := Finset.univ)
          (f := fun a : α => ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖))
  unfold _root_.MIPStarRE.QPBT.opDistSq _root_.MIPStarRE.QPBT.opFamilyDistSq
  simp only [Fintype.sum_unique]
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          ((∑ a, c a • A x a) - ∑ a, c a • B x a) ψ‖ ^ 2) ≤
      _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
        (Fintype.card α : ℝ) *
          ∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖ ^ 2) :=
      _root_.LIDT.MIPStarRE.LDT.avgOver_mono μ _ _ hpoint
    _ = (Fintype.card α : ℝ) * _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
        ∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖ ^ 2) :=
      _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul _ _ _
