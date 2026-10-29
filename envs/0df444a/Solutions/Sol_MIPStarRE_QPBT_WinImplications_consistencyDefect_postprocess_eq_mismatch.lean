-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.consistencyDefect_postprocess_eq_mismatch
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:12:24.498329+00:00
-- url     : https://prove2.me/submissions/cb5f2962-6822-42f7-adbe-61f9e4995aab

-- Generated proof for MIPStarRE.QPBT.WinImplications.consistencyDefect_postprocess_eq_mismatch.
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
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Mathlib

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
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

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



































end MIPStarRE.QPBT.DistanceCalculus

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

/-!
# Averaging lemmas for winning implications

This module derives the finite conditioning and fixed-edge rejection bounds
used by all seven exact winning implications.

## References

The formalization-only averaging and conditioning auxiliaries support items 1–7
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications

theorem solution
    {G : _root_.MIPStarRE.QPBT.Game} {X β : Type*} [Fintype X] [DecidableEq X]
    [Fintype β] [DecidableEq β]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (S : _root_.MIPStarRE.QPBT.Strategy G)
    (qA : X → G.QuestionA) (qB : X → G.QuestionB)
    (fA : X → G.AnswerA → β) (fB : X → G.AnswerB → β) :
    _root_.MIPStarRE.QPBT.consistencyDefect μ
        (fun x c => _root_.MIPStarRE.QPBT.heteroKron (((S.A (qA x)).postprocess (fA x)).effect c) 1)
        (fun x c => _root_.MIPStarRE.QPBT.heteroKron 1 (((S.B (qB x)).postprocess (fB x)).effect c))
        S.ψ =
      _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => _root_.MIPStarRE.QPBT.outcomeEventWeight S (qA x) (qB x)
        (fun a b => fA x a ≠ fB x b)) := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect _root_.MIPStarRE.QPBT.outcomeEventWeight
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm,
    _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq]
  have hmass (c d : β) :
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.ψ
          (_root_.MIPStarRE.QPBT.heteroKron
            (∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
              (S.A (qA x)).effect a)
            (∑ b ∈ Finset.univ.filter (fun b => fB x b = d),
              (S.B (qB x)).effect b)) =
        ∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
          ∑ b ∈ Finset.univ.filter (fun b => fB x b = d),
            _root_.MIPStarRE.QPBT.outcomeWeight S (qA x) (qB x) a b := by
    have hop :
        _root_.MIPStarRE.QPBT.heteroKron
            (∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
              (S.A (qA x)).effect a)
            (∑ b ∈ Finset.univ.filter (fun b => fB x b = d),
              (S.B (qB x)).effect b) =
          ∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
            ∑ b ∈ Finset.univ.filter (fun b => fB x b = d),
              _root_.MIPStarRE.QPBT.heteroKron ((S.A (qA x)).effect a) ((S.B (qB x)).effect b) := by
      ext i j
      simp only [Matrix.sum_apply, _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker,
        Matrix.kroneckerMap_apply]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    rw [hop]
    simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.outcomeWeight, _root_.MIPStarRE.QPBT.applyOperatorToState]
  simp_rw [hmass]
  symm
  calc
    (∑ a, ∑ b, if fA x a ≠ fB x b then
        _root_.MIPStarRE.QPBT.outcomeWeight S (qA x) (qB x) a b else 0) =
        ∑ a, ∑ b,
          if fA x a = fB x b then 0 else _root_.MIPStarRE.QPBT.outcomeWeight S (qA x) (qB x) a b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : fA x a = fB x b <;> simp [hab]
    _ = ∑ c : β, ∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
          ∑ b, if fA x a = fB x b then 0 else
            _root_.MIPStarRE.QPBT.outcomeWeight S (qA x) (qB x) a b := by
      exact (Finset.sum_fiberwise Finset.univ (fA x)
        (fun a => ∑ b, if fA x a = fB x b then 0 else
          _root_.MIPStarRE.QPBT.outcomeWeight S (qA x) (qB x) a b)).symm
    _ = ∑ c : β, ∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
          ∑ b, if c = fB x b then 0 else _root_.MIPStarRE.QPBT.outcomeWeight S (qA x) (qB x) a b := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ c : β, ∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
          ∑ d : β, ∑ b ∈ Finset.univ.filter (fun b => fB x b = d),
            if c = fB x b then 0 else _root_.MIPStarRE.QPBT.outcomeWeight S (qA x) (qB x) a b := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      exact (Finset.sum_fiberwise Finset.univ (fB x)
        (fun b => if c = fB x b then 0 else
          _root_.MIPStarRE.QPBT.outcomeWeight S (qA x) (qB x) a b)).symm
    _ = ∑ c : β, ∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
          ∑ d : β, ∑ b ∈ Finset.univ.filter (fun b => fB x b = d),
            if c = d then 0 else _root_.MIPStarRE.QPBT.outcomeWeight S (qA x) (qB x) a b := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro b hb
      rw [(Finset.mem_filter.mp hb).2]
    _ = ∑ c : β, ∑ d : β,
          ∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
            ∑ b ∈ Finset.univ.filter (fun b => fB x b = d),
              if c = d then 0 else _root_.MIPStarRE.QPBT.outcomeWeight S (qA x) (qB x) a b := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ c : β, ∑ d : β, if c = d then 0 else
          ∑ a ∈ Finset.univ.filter (fun a => fA x a = c),
            ∑ b ∈ Finset.univ.filter (fun b => fB x b = d),
              _root_.MIPStarRE.QPBT.outcomeWeight S (qA x) (qB x) a b := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      by_cases hcd : c = d <;> simp [hcd]
