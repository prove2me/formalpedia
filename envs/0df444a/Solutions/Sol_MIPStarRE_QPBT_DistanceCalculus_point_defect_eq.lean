-- Prove2me | solution 1 for MIPStarRE.QPBT.DistanceCalculus.point_defect_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:40:57.108056+00:00
-- url     : https://prove2.me/submissions/77533490-2009-4c62-b392-5cf83e687908

-- Generated proof for MIPStarRE.QPBT.DistanceCalculus.point_defect_eq.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
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



































/-- The state quadratic form commutes with a finite sum. -/
private theorem stateQForm_sum {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : α → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (∑ a, M a) = ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M a) := by
  simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]

/-- The quadratic form of the identity is the squared vector norm. -/
theorem stateQForm_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) = ‖ψ‖ ^ 2 := by
  have hone : _root_.MIPStarRE.QPBT.applyOperatorToState (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ψ = ψ := by
    simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, hone]
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) ψ)









/-- Removing the diagonal term from a finite sum is subtraction of that term. -/
private theorem sum_if_eq_zero_else {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (a : α) :
    (∑ b : α, if a = b then 0 else f b) = (∑ b : α, f b) - f a := by
  have herase := Finset.sum_erase_add (Finset.univ : Finset α) f
    (Finset.mem_univ a)
  calc
    (∑ b : α, if a = b then 0 else f b) =
        ∑ b ∈ (Finset.univ : Finset α).filter (fun b => b ≠ a), f b := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : a = b <;> simp [h, Ne.symm]
    _ = ∑ b ∈ (Finset.univ : Finset α).erase a, f b := by
      rw [Finset.filter_ne']
    _ = (∑ b : α, f b) - f a := by linarith

/-- Summing a complete measurement in the right factor leaves the first operator. -/
private theorem stateQForm_mul_sum_right {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (B : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (∑ b : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M * B.effect b)) = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  rw [← stateQForm_sum, ← Finset.mul_sum, B.sum_eq_one, mul_one]

/-- The quadratic forms of all effects sum to the squared vector norm. -/
private theorem stateQForm_effect_sum {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (A : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) :
    (∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a)) = ‖ψ‖ ^ 2 := by
  rw [← stateQForm_sum, A.sum_eq_one, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_one]







































end MIPStarRE.QPBT.DistanceCalculus

/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

theorem solution {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (A B : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) :
    (∑ a : α, ∑ b : α,
      if a = b then 0 else _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a * B.effect b)) =
      ‖ψ‖ ^ 2 - ∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a * B.effect a) := by
  calc
    _ = ∑ a : α, ((∑ b : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a * B.effect b)) -
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a * B.effect a)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact sum_if_eq_zero_else
        (fun b => _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a * B.effect b)) a
    _ = ∑ a : α, (_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a) -
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a * B.effect a)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [stateQForm_mul_sum_right B ψ]
    _ = (∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a)) -
          ∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a * B.effect a) := by
      rw [Finset.sum_sub_distrib]
    _ = _ := by rw [stateQForm_effect_sum]
