-- Prove2me | solution 1 for MIPStarRE.QPBT.SandwichProduct.diagonal_postprocess_stateQForm_eq_pair_sum
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:45:51.3731+00:00
-- url     : https://prove2.me/submissions/e40f5570-ec68-4ac8-8fde-8383e5c80648

-- Generated proof for MIPStarRE.QPBT.SandwichProduct.diagonal_postprocess_stateQForm_eq_pair_sum.
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
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.SandwichProduct
end MIPStarRE.QPBT.SandwichProduct

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



























/-- The state quadratic form is additive over finite sums of operators. This is
the formalization-only identity `lem:distance-qform-finset-sum`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset β) (M : β → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (∑ b ∈ s, M b) = ∑ b ∈ s, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M b) := by
  simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]































































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

theorem solution
    {α β ιA ιB : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (f : α → β) :
    (∑ b : β, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
      (_root_.MIPStarRE.QPBT.heteroKron ((A.postprocess f).effect b) ((B.postprocess f).effect b))) =
      ∑ a : α, ∑ a' : α, if f a = f a' then
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (A.effect a) (B.effect a')) else 0 := by
  classical
  have hterm (b : β) : _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
      (_root_.MIPStarRE.QPBT.heteroKron ((A.postprocess f).effect b) ((B.postprocess f).effect b)) =
      ∑ a : α, ∑ a' : α, if f a = b ∧ f a' = b then
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (A.effect a) (B.effect a')) else 0 := by
    rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
      _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
      _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hab : f a = b
    · rw [if_pos hab, _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a' _
      by_cases ha'b : f a' = b <;> simp [hab, ha'b]
    · simp [hab]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a' _
  by_cases haa' : f a = f a'
  · rw [haa']
    simp
  · apply Eq.trans (Finset.sum_eq_zero (fun b _ => by
      simp only [ite_eq_right_iff]
      intro hpair
      exact (haa' (hpair.1.trans hpair.2.symm)).elim))
    simp [haa']
