-- Prove2me | solution 1 for MIPStarRE.QPBT.DistanceCalculus.point_distance_le_two_defect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:02:02.043757+00:00
-- url     : https://prove2.me/submissions/8604134d-0f23-4d84-81da-23f781dcee3c

-- Generated proof for MIPStarRE.QPBT.DistanceCalculus.point_distance_le_two_defect.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_point_defect_eq
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono

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

/-- The squared norm of `M ψ` is the quadratic form of `Mᴴ M`. -/
private theorem norm_applyOperatorToState_sq_eq {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState M ψ‖ ^ 2 =
      (inner ℂ ψ (_root_.MIPStarRE.QPBT.applyOperatorToState (Mᴴ * M) ψ)).re := by
  rw [@norm_sq_eq_re_inner ℂ]
  unfold _root_.MIPStarRE.QPBT.applyOperatorToState
  rw [_root_.LIDT.Matrix.toEuclideanLin_conjTranspose_mul_self]
  change (inner ℂ (Matrix.toEuclideanLin M ψ) (Matrix.toEuclideanLin M ψ)).re =
    (inner ℂ ψ ((Matrix.toEuclideanLin M).adjoint (Matrix.toEuclideanLin M ψ))).re
  rw [LinearMap.adjoint_inner_right]































/-- The state quadratic form preserves operator subtraction. -/
private theorem stateQForm_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M N : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M - N) = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M - _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ N := by
  simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]

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



/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): every effect of a complete measurement is bounded by the identity. -/
theorem measurement_effect_le_one {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (a : α) :
    M.effect a ≤ 1 := by
  calc
    M.effect a ≤ ∑ b : α, M.effect b :=
      Finset.single_le_sum (fun b _ => M.pos b) (Finset.mem_univ a)
    _ = 1 := M.sum_eq_one



/-- Expand the squared state-dependent distance between two measurement effects. -/
private theorem norm_effect_sub_effect_sq_expand {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (A B : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (a : α) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A.effect a - B.effect a) ψ‖ ^ 2 =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a * A.effect a) +
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (B.effect a * B.effect a) -
      2 * _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a * B.effect a) := by
  rw [norm_applyOperatorToState_sq_eq]
  change _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A.effect a - B.effect a)ᴴ *
    (A.effect a - B.effect a)) = _
  rw [show (A.effect a - B.effect a)ᴴ * (A.effect a - B.effect a) =
      A.effect a * A.effect a - B.effect a * A.effect a -
        (A.effect a * B.effect a - B.effect a * B.effect a) by
    simp only [Matrix.conjTranspose_sub, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian A a,
      _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian B a]
    noncomm_ring]
  rw [stateQForm_sub, stateQForm_sub, stateQForm_sub]
  have hcross : _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (B.effect a * A.effect a) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a * B.effect a) := by
    unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm _root_.MIPStarRE.QPBT.applyOperatorToState
    rw [show B.effect a * A.effect a = (A.effect a * B.effect a)ᴴ by
      simp [Matrix.conjTranspose_mul, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian A a,
        _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian B a]]
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      LinearMap.adjoint_inner_right]
    simpa using (inner_re_symm (𝕜 := ℂ)
      ((Matrix.toEuclideanLin (A.effect a * B.effect a)) ψ) ψ)
  rw [hcross]
  ring





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

theorem solution {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (A B : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) :
    (∑ a : α, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A.effect a - B.effect a) ψ‖ ^ 2) ≤
      2 * (∑ a : α, ∑ b : α,
        if a = b then 0 else _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a * B.effect b)) := by
  have hterm (a : α) :
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A.effect a - B.effect a) ψ‖ ^ 2 ≤
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a) + _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (B.effect a) -
          2 * _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a * B.effect a) := by
    rw [norm_effect_sub_effect_sq_expand A B ψ a]
    have hA := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono
      (_root_.LIDT.MIPStarRE.Quantum.sq_le_self (A.pos a) (_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_le_one A a)) ψ
    have hB := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono
      (_root_.LIDT.MIPStarRE.Quantum.sq_le_self (B.pos a) (_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_le_one B a)) ψ
    exact sub_le_sub_right (add_le_add hA hB) _
  calc
    _ ≤ ∑ a : α, (_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a) + _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (B.effect a) -
          2 * _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a * B.effect a)) :=
      Finset.sum_le_sum fun a _ => hterm a
    _ = (∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a)) +
          (∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (B.effect a)) -
          2 * (∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a * B.effect a)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = 2 * (‖ψ‖ ^ 2 -
          ∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a * B.effect a)) := by
      rw [stateQForm_effect_sum A ψ, stateQForm_effect_sum B ψ]
      ring
    _ = _ := by rw [_root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq A B ψ]
