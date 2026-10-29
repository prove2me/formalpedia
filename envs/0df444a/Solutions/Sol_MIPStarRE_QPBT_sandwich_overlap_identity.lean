-- Prove2me | solution 1 for MIPStarRE.QPBT.sandwich_overlap_identity
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:06:37.564439+00:00
-- url     : https://prove2.me/submissions/3ce94903-486a-408e-b11e-1987b7a519e7

-- Generated proof for MIPStarRE.QPBT.sandwich_overlap_identity.
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
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_point_defect_eq
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
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Combining/Points/Consistency.lean. -/
/-!
# Self-consistency of the sandwich POVM

The sandwich POVM `R^{x,z}_{a,b} = M^Z_b M^X_a M^Z_b` of
`MIPStarRE/QPBT/Combining/Points/Sandwich.lean` is approximately self-consistent
between opposite register placements.  The source establishes this by a
Cauchy--Schwarz chain (displays `eq:qld-rw-self-cons-1` to
`eq:qld-rw-self-cons-4`); here an exact identity is used instead.  Writing
`P_1, P_2` for the two placements of an operator `P`,
`W_b = (M^Z_b)_1 (M^Z_b)_2`, and `D^W_c = (M^W_c)_1 - (M^W_c)_2`, the
consistency defect of the two placed sandwiches equals
`(1/2) ∑_b ‖D^Z_b ψ‖^2 + (1/2) ∑_{a,b} ‖D^X_a W_b ψ‖^2`,
by two applications of the identity
`∑_c ⟨w, P_c Q_c w⟩ = ‖w‖^2 - (1/2) ∑_c ‖(P_c - Q_c) w‖^2` for projective
measurements.  The second sum is then bounded by the self-consistency of `M^X`
and the commutators on the two placements, since
`D^X_a W_b = W_b D^X_a + (M^Z_b)_2 K^1_{a,b} - (M^Z_b)_1 K^2_{a,b}`, where
`K^i_{a,b}` is the placed commutator of `M^X_a` and `M^Z_b`.

## Main results

* `sandwich_overlap_identity`: the exact expression of the overlap of two
  placed sandwiches.
* `sandwich_defect_pointwise_le`: the pointwise bound on the consistency
  defect of the sandwich for a fixed point pair.
* `ProjectiveSetting.sandwichDefectBound`,
  `ProjectiveSetting.sandwich_offDiagonal_le_sandwichDefectBound`, and
  `ProjectiveSetting.avg_sandwichDefectBound_le`: the bound as a function of
  the point pair, the pointwise estimate, and the average.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:743-790`,
blueprint `blueprint/src/chapter/ch15_qpbt_combining.tex:851-880`
(`lem:qld-4-10`, first step); the identity route is explained in
`docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## Quadratic-form identities -/

/-- The squared norm of `W ψ` is the quadratic form of `Wᴴ W`. -/
theorem norm_applyOperatorToState_sq_eq_stateQForm {ι : Type*} [Fintype ι]
    [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) (W : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState W ψ‖ ^ 2 = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (Wᴴ * W) :=
  _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_sq W ψ

/-- For two projective measurements, the diagonal overlap in a vector `w` is
the squared norm of `w` minus half the summed squared distances.  This is the
identity behind `fact:agreement` for projective families, blueprint
`blueprint/src/chapter/ch12_qpbt_games.tex:260-272`. -/
theorem sum_stateQForm_mul_eq_of_projective {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (A B : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (w : EuclideanSpace ℂ ι)
    (hA : _root_.MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : _root_.MIPStarRE.QPBT.Measurement.IsProjective B) :
    ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm w (A.effect a * B.effect a) =
      ‖w‖ ^ 2 -
        (1 / 2) * ∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A.effect a - B.effect a) w‖ ^ 2 := by
  classical
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.point_distance_eq_two_defect_of_projective A B w hA hB, _root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq]
  ring





/-! ## The overlap of two placed sandwiches -/

section Abstract

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]

/-- Formalization-only auxiliary for `lem:qld-4-10`: the product of the two
placed sandwiches is `W_bᴴ (X_1 X_2) W_b` with `W_b = Z_1 Z_2`, whenever the
operators of the two placements commute. -/
theorem sandwich_mul_sandwich_eq (X₁ X₂ : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (Z₁ Z₂ : _root_.LIDT.MIPStarRE.Quantum.Measurement β ι)
    (hXZ : ∀ a b, X₁.effect a * Z₂.effect b = Z₂.effect b * X₁.effect a)
    (hZX : ∀ a b, Z₁.effect b * X₂.effect a = X₂.effect a * Z₁.effect b)
    (hZZ : ∀ b, Z₁.effect b * Z₂.effect b = Z₂.effect b * Z₁.effect b)
    (a : α) (b : β) :
    (Z₁.effect b * X₁.effect a * Z₁.effect b) *
        (Z₂.effect b * X₂.effect a * Z₂.effect b) =
      (Z₁.effect b * Z₂.effect b)ᴴ * (X₁.effect a * X₂.effect a) *
        (Z₁.effect b * Z₂.effect b) := by
  rw [Matrix.conjTranspose_mul, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian,
    _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
  simp only [Matrix.mul_assoc]
  rw [(show Commute (Z₁.effect b) (Z₂.effect b) from hZZ b).left_comm
      (X₂.effect a * Z₂.effect b),
    (show Commute (X₁.effect a) (Z₂.effect b) from hXZ a b).left_comm,
    (show Commute (Z₁.effect b) (Z₂.effect b) from hZZ b).left_comm,
    (show Commute (Z₁.effect b) (X₂.effect a) from hZX a b).left_comm]







end Abstract

/-! ## The bound for the placed sandwiches -/



end

end MIPStarRE.QPBT

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







































/-- The quadratic form of `Wᴴ M W` in `ψ` is the quadratic form of `M` in
`W ψ`.  This is the conjugation identity behind the placed-sandwich
rewritings: conjugating transfers the outer operator to the state vector.
It is formalization-only auxiliary content, shared by the overlap-gap estimate
and the sandwich self-consistency argument. -/
theorem stateQForm_conjTranspose_mul_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (W M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (Wᴴ * M * W) = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.applyOperatorToState W ψ) M := by
  unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
  congr 1
  change inner ℂ ψ (Matrix.toEuclideanLin Wᴴ _) =
    inner ℂ (Matrix.toEuclideanLin W ψ) _
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]



















































end MIPStarRE.QPBT.DistanceCalculus

/-!
# Self-consistency of the sandwich POVM

The sandwich POVM `R^{x,z}_{a,b} = M^Z_b M^X_a M^Z_b` of
`MIPStarRE/QPBT/Combining/Points/Sandwich.lean` is approximately self-consistent
between opposite register placements.  The source establishes this by a
Cauchy--Schwarz chain (displays `eq:qld-rw-self-cons-1` to
`eq:qld-rw-self-cons-4`); here an exact identity is used instead.  Writing
`P_1, P_2` for the two placements of an operator `P`,
`W_b = (M^Z_b)_1 (M^Z_b)_2`, and `D^W_c = (M^W_c)_1 - (M^W_c)_2`, the
consistency defect of the two placed sandwiches equals
`(1/2) ∑_b ‖D^Z_b ψ‖^2 + (1/2) ∑_{a,b} ‖D^X_a W_b ψ‖^2`,
by two applications of the identity
`∑_c ⟨w, P_c Q_c w⟩ = ‖w‖^2 - (1/2) ∑_c ‖(P_c - Q_c) w‖^2` for projective
measurements.  The second sum is then bounded by the self-consistency of `M^X`
and the commutators on the two placements, since
`D^X_a W_b = W_b D^X_a + (M^Z_b)_2 K^1_{a,b} - (M^Z_b)_1 K^2_{a,b}`, where
`K^i_{a,b}` is the placed commutator of `M^X_a` and `M^Z_b`.

## Main results

* `sandwich_overlap_identity`: the exact expression of the overlap of two
  placed sandwiches.
* `sandwich_defect_pointwise_le`: the pointwise bound on the consistency
  defect of the sandwich for a fixed point pair.
* `ProjectiveSetting.sandwichDefectBound`,
  `ProjectiveSetting.sandwich_offDiagonal_le_sandwichDefectBound`, and
  `ProjectiveSetting.avg_sandwichDefectBound_le`: the bound as a function of
  the point pair, the pointwise estimate, and the average.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:743-790`,
blueprint `blueprint/src/chapter/ch15_qpbt_combining.tex:851-880`
(`lem:qld-4-10`, first step); the identity route is explained in
`docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## Quadratic-form identities -/









/-! ## The overlap of two placed sandwiches -/



variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]

theorem solution (ψ : EuclideanSpace ℂ ι)
    (X₁ X₂ : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (Z₁ Z₂ : _root_.LIDT.MIPStarRE.Quantum.Measurement β ι)
    (hX₁ : _root_.MIPStarRE.QPBT.Measurement.IsProjective X₁)
    (hX₂ : _root_.MIPStarRE.QPBT.Measurement.IsProjective X₂)
    (hZ₁ : _root_.MIPStarRE.QPBT.Measurement.IsProjective Z₁)
    (hZ₂ : _root_.MIPStarRE.QPBT.Measurement.IsProjective Z₂)
    (hXZ : ∀ a b, X₁.effect a * Z₂.effect b = Z₂.effect b * X₁.effect a)
    (hZX : ∀ a b, Z₁.effect b * X₂.effect a = X₂.effect a * Z₁.effect b)
    (hZZ : ∀ b, Z₁.effect b * Z₂.effect b = Z₂.effect b * Z₁.effect b) :
    ∑ ab : α × β, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        ((Z₁.effect ab.2 * X₁.effect ab.1 * Z₁.effect ab.2) *
          (Z₂.effect ab.2 * X₂.effect ab.1 * Z₂.effect ab.2)) =
      ‖ψ‖ ^ 2 -
        (1 / 2) * ∑ b, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (Z₁.effect b - Z₂.effect b) ψ‖ ^ 2 -
        (1 / 2) * ∑ ab : α × β, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (X₁.effect ab.1 - X₂.effect ab.1)
          (_root_.MIPStarRE.QPBT.applyOperatorToState (Z₁.effect ab.2 * Z₂.effect ab.2) ψ)‖ ^ 2 := by
  have hW : ∀ b, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (Z₁.effect b * Z₂.effect b) ψ‖ ^ 2 =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (Z₁.effect b * Z₂.effect b) := by
    intro b
    rw [_root_.MIPStarRE.QPBT.norm_applyOperatorToState_sq_eq_stateQForm, Matrix.conjTranspose_mul,
      _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
    congr 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Z₁.effect b) (Z₁.effect b),
      (hZ₁ b).isIdempotentElem.eq, hZZ b, ← Matrix.mul_assoc,
      (hZ₂ b).isIdempotentElem.eq]
  have hstep : ∀ ab : α × β, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
      ((Z₁.effect ab.2 * X₁.effect ab.1 * Z₁.effect ab.2) *
        (Z₂.effect ab.2 * X₂.effect ab.1 * Z₂.effect ab.2)) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.applyOperatorToState (Z₁.effect ab.2 * Z₂.effect ab.2) ψ)
        (X₁.effect ab.1 * X₂.effect ab.1) := by
    intro ab
    rw [_root_.MIPStarRE.QPBT.sandwich_mul_sandwich_eq X₁ X₂ Z₁ Z₂ hXZ hZX hZZ,
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_conjTranspose_mul_mul]
  have hWsum : ∑ b, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (Z₁.effect b * Z₂.effect b) ψ‖ ^ 2 =
      ‖ψ‖ ^ 2 -
        (1 / 2) * ∑ b, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (Z₁.effect b - Z₂.effect b) ψ‖ ^ 2 := by
    simp_rw [hW]
    exact _root_.MIPStarRE.QPBT.sum_stateQForm_mul_eq_of_projective Z₁ Z₂ ψ hZ₁ hZ₂
  calc ∑ ab : α × β, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        ((Z₁.effect ab.2 * X₁.effect ab.1 * Z₁.effect ab.2) *
          (Z₂.effect ab.2 * X₂.effect ab.1 * Z₂.effect ab.2))
      = ∑ b, ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.applyOperatorToState (Z₁.effect b * Z₂.effect b) ψ)
          (X₁.effect a * X₂.effect a) := by
        simp_rw [hstep]
        exact Fintype.sum_prod_type_right _
    _ = ∑ b, (‖_root_.MIPStarRE.QPBT.applyOperatorToState (Z₁.effect b * Z₂.effect b) ψ‖ ^ 2 -
          (1 / 2) * ∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (X₁.effect a - X₂.effect a)
            (_root_.MIPStarRE.QPBT.applyOperatorToState (Z₁.effect b * Z₂.effect b) ψ)‖ ^ 2) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        exact _root_.MIPStarRE.QPBT.sum_stateQForm_mul_eq_of_projective X₁ X₂ _ hX₁ hX₂
    _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hWsum,
          Fintype.sum_prod_type_right]
