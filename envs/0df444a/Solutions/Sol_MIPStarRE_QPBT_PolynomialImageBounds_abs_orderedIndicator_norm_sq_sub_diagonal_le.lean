-- Prove2me | solution 1 for MIPStarRE.QPBT.PolynomialImageBounds.abs_orderedIndicator_norm_sq_sub_diagonal_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:48:41.505123+00:00
-- url     : https://prove2.me/submissions/5debb75e-bb60-460d-8575-eb3186a4501c

-- Generated proof for MIPStarRE.QPBT.PolynomialImageBounds.abs_orderedIndicator_norm_sq_sub_diagonal_le.
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
import Definitions.Def_QPBT_QPBT_Combining_PolynomialImageBounds
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Pasting_Heterogeneous
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono

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
namespace MIPStarRE.QPBT.PolynomialImageBounds
end MIPStarRE.QPBT.PolynomialImageBounds

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





























/-- A positive semidefinite operator has nonnegative state quadratic form. This
is the formalization-only order fact `lem:distance-qform-nonnegative`, used for
the nonnegative overlap terms in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) {M : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hM : 0 ≤ M) :
    0 ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  calc
    0 = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ 0 := by simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
    _ ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hM ψ







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

















































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Combining/PolynomialImageBounds.lean. -/
/-!
# Indicator-weighted ordered products

This module proves the local norm calculation in `eq:qld-g-prime`. The state
vector is not assumed normalized: its squared norm controls the exceptional
coefficient, so the estimate can be summed over all polynomial outcomes.
The measurements act on an arbitrary finite space, which includes either
player's placed expanded measurements.

The coefficient-polynomial argument also bounds mass outside the scalar-linear
image, with its actual ordered-correlation error displayed in the conclusion.
These are auxiliary estimates, not the global polynomial-pair construction.
The remaining block-separation and construction obligations are recorded in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex` and issue Dengnifer/MIPStarRE-QPBT-bak#513.

Only the dependency chain needed for these estimates is exposed; supporting
lemmas remain private.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1289-1326`,
  especially `eq:qld-g-42`, `eq:qld-g-43`, and `eq:qld-g-prime`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace PolynomialImageBounds

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]





/-- For a nonzero second coefficient, X orthogonality and cancellation in
the field eliminate every off-diagonal term of the ordered Gram operator.
This is the exact local algebra behind `eq:qld-g-prime`; no commutation of
the X and Z measurements is assumed. -/
private theorem orderedIndicator_gram_of_ne_zero (X Z : _root_.LIDT.MIPStarRE.Quantum.Measurement F ι)
    (hX : _root_.MIPStarRE.QPBT.Measurement.IsProjective X) (α β a : F) (hβ : β ≠ 0) :
    (_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β a)ᴴ * _root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β a =
      _root_.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator X Z α β a := by
  classical
  unfold _root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator _root_.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator
  rw [Matrix.conjTranspose_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun bc _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single bc]
  · by_cases h : α * bc.1 + β * bc.2 = a
    · simp only [if_pos h, Matrix.conjTranspose_mul, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
      rw [mul_assoc (Z.effect bc.2), ← mul_assoc (X.effect bc.1),
        (hX bc.1).isIdempotentElem.eq, ← mul_assoc]
    · simp [h]
  · intro bc' _ hne
    by_cases h : α * bc.1 + β * bc.2 = a
    · by_cases h' : α * bc'.1 + β * bc'.2 = a
      · have hb : bc.1 ≠ bc'.1 := by
          intro hb
          have hc : bc.2 = bc'.2 := mul_left_cancel₀ hβ (by
            apply add_left_cancel (a := α * bc.1)
            simpa only [hb] using h.trans h'.symm)
          exact hne (Prod.ext hb hc).symm
        simp only [if_pos h, if_pos h', Matrix.conjTranspose_mul,
          _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
        calc
          Z.effect bc.2 * X.effect bc.1 * (X.effect bc'.1 * Z.effect bc'.2) =
              Z.effect bc.2 * (X.effect bc.1 * X.effect bc'.1) * Z.effect bc'.2 := by
            simp only [mul_assoc]
          _ = 0 := by rw [_root_.MIPStarRE.QPBT.DistanceCalculus.projective_effect_mul_effect_eq_zero X hX hb]; simp
      · simp [h']
    · simp [h]
  · simp

/-- The squared state norm of the ordered indicator equals its diagonal
sandwich quadratic form when the second coefficient is nonzero. -/
private theorem orderedIndicator_norm_sq_of_ne_zero (X Z : _root_.LIDT.MIPStarRE.Quantum.Measurement F ι)
    (hX : _root_.MIPStarRE.QPBT.Measurement.IsProjective X) (α β a : F) (hβ : β ≠ 0)
    (ψ : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β a) ψ‖ ^ 2 =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator X Z α β a) := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_sq,
    orderedIndicator_gram_of_ne_zero X Z hX α β a hβ]
  rfl

/-- The diagonal indicator is a positive contraction, since it selects
effects from the complete sandwich POVM. -/
private theorem diagonalIndicator_bounds (X Z : _root_.LIDT.MIPStarRE.Quantum.Measurement F ι)
    (hZ : _root_.MIPStarRE.QPBT.Measurement.IsProjective Z) (α β a : F) :
    0 ≤ _root_.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator X Z α β a ∧ _root_.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator X Z α β a ≤ 1 := by
  obtain ⟨hpos, hsum⟩ := _root_.MIPStarRE.QPBT.pastedMeasurement_isMeasurement X Z hZ
  change (∀ bc : F × F, 0 ≤ Z.effect bc.2 * X.effect bc.1 * Z.effect bc.2) at hpos
  change (∑ bc : F × F, Z.effect bc.2 * X.effect bc.1 * Z.effect bc.2) = 1 at hsum
  constructor
  · exact Finset.sum_nonneg fun bc _ => by
      split_ifs
      · exact hpos bc
      · exact le_refl 0
  · calc
      _root_.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator X Z α β a ≤
          ∑ bc : F × F, Z.effect bc.2 * X.effect bc.1 * Z.effect bc.2 := by
        refine Finset.sum_le_sum fun bc _ => ?_
        split_ifs
        · exact le_refl _
        · exact hpos bc
      _ = 1 := hsum

/-- At the exceptional coefficient zero, completeness of Z leaves a
coarse-grained X projection. This includes zero first coefficient. -/
private theorem orderedIndicator_zero (X Z : _root_.LIDT.MIPStarRE.Quantum.Measurement F ι) (α a : F) :
    _root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α 0 a = (X.postprocess (fun b => α * b)).effect a := by
  unfold _root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator
  rw [Fintype.sum_prod_type, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : α * b = a
  · simp only [zero_mul, add_zero, h, if_true]
    rw [← Finset.mul_sum, Z.sum_eq_one, mul_one]
  · simp [h]

/-- Every linear-answer ordered indicator is a contraction. For nonzero
second coefficient this follows from the diagonal identity; at zero it
follows from completeness and projective postprocessing. -/
theorem orderedIndicator_gram_le_one (X Z : _root_.LIDT.MIPStarRE.Quantum.Measurement F ι)
    (hX : _root_.MIPStarRE.QPBT.Measurement.IsProjective X) (hZ : _root_.MIPStarRE.QPBT.Measurement.IsProjective Z) (α β a : F) :
    (_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β a)ᴴ * _root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β a ≤ 1 := by
  by_cases hβ : β = 0
  · subst β
    rw [orderedIndicator_zero, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian,
      (_root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective X hX (fun b => α * b) a).isIdempotentElem.eq]
    exact _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_le_one _ _
  · rw [orderedIndicator_gram_of_ne_zero X Z hX α β a hβ]
    exact (diagonalIndicator_bounds X Z hZ α β a).2

































end PolynomialImageBounds

end

end MIPStarRE.QPBT

/-!
# Indicator-weighted ordered products

This module proves the local norm calculation in `eq:qld-g-prime`. The state
vector is not assumed normalized: its squared norm controls the exceptional
coefficient, so the estimate can be summed over all polynomial outcomes.
The measurements act on an arbitrary finite space, which includes either
player's placed expanded measurements.

The coefficient-polynomial argument also bounds mass outside the scalar-linear
image, with its actual ordered-correlation error displayed in the conclusion.
These are auxiliary estimates, not the global polynomial-pair construction.
The remaining block-separation and construction obligations are recorded in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex` and issue Dengnifer/MIPStarRE-QPBT-bak#513.

Only the dependency chain needed for these estimates is exposed; supporting
lemmas remain private.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1289-1326`,
  especially `eq:qld-g-42`, `eq:qld-g-43`, and `eq:qld-g-prime`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



open MIPStarRE.QPBT.PolynomialImageBounds

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]

theorem solution (X Z : _root_.LIDT.MIPStarRE.Quantum.Measurement F ι)
    (hX : _root_.MIPStarRE.QPBT.Measurement.IsProjective X) (hZ : _root_.MIPStarRE.QPBT.Measurement.IsProjective Z)
    (α β a : F) (ψ : EuclideanSpace ℂ ι) :
    |‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β a) ψ‖ ^ 2 -
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator X Z α β a)| ≤
      if β = 0 then ‖ψ‖ ^ 2 else 0 := by
  by_cases hβ : β = 0
  · rw [if_pos hβ]
    have hA0 := sq_nonneg ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β a) ψ‖
    have hA1 : ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β a) ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
      rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_sq, ← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_one ψ]
      exact _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono (_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator_gram_le_one X Z hX hZ α β a) ψ
    have hD := diagonalIndicator_bounds X Z hZ α β a
    have hD0 := _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg ψ hD.1
    have hD1 : _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator X Z α β a) ≤ ‖ψ‖ ^ 2 := by
      rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_one ψ]
      exact _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hD.2 ψ
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [if_neg hβ, orderedIndicator_norm_sq_of_ne_zero X Z hX α β a hβ ψ]
    simp
