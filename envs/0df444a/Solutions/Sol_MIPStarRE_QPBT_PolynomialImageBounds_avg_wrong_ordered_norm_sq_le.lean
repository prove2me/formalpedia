-- Prove2me | solution 1 for MIPStarRE.QPBT.PolynomialImageBounds.avg_wrong_ordered_norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:48:41.693627+00:00
-- url     : https://prove2.me/submissions/208f179c-1453-4688-9b56-8f9fc56e1e1a

-- Generated proof for MIPStarRE.QPBT.PolynomialImageBounds.avg_wrong_ordered_norm_sq_le.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Combining_PolynomialImageBounds
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Pasting_Heterogeneous
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_affine_collision_average

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Distribution.IsProbability
end LIDT.MIPStarRE.LDT.Distribution.IsProbability
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace LIDT.MIPStarRE.Quantum.Measurement
end LIDT.MIPStarRE.Quantum.Measurement
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
namespace MIPStarRE.QPBT.PolynomialImageBounds
end MIPStarRE.QPBT.PolynomialImageBounds

/- Source helpers from QPBT/Combining/RetainedPointBounds.lean. -/
/-!
# Retained point mismatch from ordered estimates

The incorrect point projection is the outer factor of the ordered product.
The scalar collision identity then bounds its average image norm without an
outcome-count factor. All vectors remain unnormalized.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1360-1404`,
`eq:qld-s-good-and-bad` through `eq:qld-sgg-mhat-sandwich`;
blueprint `lem:qld-4-7`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.PolynomialImageBounds

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]

omit [Field F] in
private theorem wrong_mul_effect (X : _root_.LIDT.MIPStarRE.Quantum.Measurement F ι)
    (hX : _root_.MIPStarRE.QPBT.Measurement.IsProjective X) (r b : F) :
    (1 - X.effect r) * X.effect b = if b = r then 0 else X.effect b := by
  by_cases h : b = r
  · simp [h, sub_mul, (hX r).isIdempotentElem.eq]
  · rw [sub_mul, one_mul, _root_.MIPStarRE.QPBT.DistanceCalculus.projective_effect_mul_effect_eq_zero X hX (Ne.symm h)]
    simp [h]

private theorem wrong_ordered_gram (X Z : _root_.LIDT.MIPStarRE.Quantum.Measurement F ι)
    (hX : _root_.MIPStarRE.QPBT.Measurement.IsProjective X) (r α β a : F) (hβ : β ≠ 0) :
    let T := (1 - X.effect r) * _root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β a
    Tᴴ * T = ∑ bc : F × F,
      if α * bc.1 + β * bc.2 = a ∧ bc.1 ≠ r then
        Z.effect bc.2 * X.effect bc.1 * Z.effect bc.2 else 0 := by
  classical
  have hexpand : (1 - X.effect r) * _root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β a =
      ∑ bc : F × F, if α * bc.1 + β * bc.2 = a ∧ bc.1 ≠ r then
        X.effect bc.1 * Z.effect bc.2 else 0 := by
    rw [_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro bc _
    by_cases h : α * bc.1 + β * bc.2 = a
    · simp only [h, if_true, true_and, ← mul_assoc, wrong_mul_effect X hX]
      split_ifs <;> simp_all
    · simp [h]
  dsimp only
  rw [hexpand, Matrix.conjTranspose_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun bc _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single bc]
  · by_cases h : α * bc.1 + β * bc.2 = a ∧ bc.1 ≠ r
    · simp only [if_pos h, Matrix.conjTranspose_mul, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
      rw [mul_assoc (Z.effect bc.2), ← mul_assoc (X.effect bc.1),
        (hX bc.1).isIdempotentElem.eq, ← mul_assoc]
    · simp [h]
  · intro bc' _ hne
    by_cases h : α * bc.1 + β * bc.2 = a ∧ bc.1 ≠ r
    · by_cases h' : α * bc'.1 + β * bc'.2 = a ∧ bc'.1 ≠ r
      · have hb : bc.1 ≠ bc'.1 := by
          intro hb
          have hc : bc.2 = bc'.2 := mul_left_cancel₀ hβ (by
            apply add_left_cancel (a := α * bc.1)
            simpa only [hb] using h.1.trans h'.1.symm)
          exact hne (Prod.ext hb hc).symm
        simp only [if_pos h, if_pos h', Matrix.conjTranspose_mul,
          _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
        calc
          _ = Z.effect bc.2 * (X.effect bc.1 * X.effect bc'.1) * Z.effect bc'.2 := by
            simp only [mul_assoc]
          _ = 0 := by rw [_root_.MIPStarRE.QPBT.DistanceCalculus.projective_effect_mul_effect_eq_zero X hX hb]; simp
      · simp [h']
    · simp [h]
  · simp





end

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



























/-- The state quadratic form is additive over finite sums of operators. This is
the formalization-only identity `lem:distance-qform-finset-sum`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset β) (M : β → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (∑ b ∈ s, M b) = ∑ b ∈ s, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M b) := by
  simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]

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

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/GroundSlice.lean. -/
/-!
# Contractions, isometries and the ground slice of the dilation

Support for the transfer step of `thm:ms-rigidity` (blueprint
`thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`):
the calculus needed to compare the dilated projective strategy of
`Rigidity/Dilation.lean` with the original strategy on states.

* Contractions: operators `K` with `Kᴴ K ≤ 1` do not increase norms; effects,
  observables of binary measurements, orthogonal projections, tensor placements,
  products and isometry conjugates are contractions.
* Matrices of isometries: `Vᴴ V = 1`, the two-sided isometry image of a state
  preserves norms, and a conjugated local operator acts on the transported state
  as the original operator acts on the original state.
* The ground projection `Π` of an enlarged local space: an orthogonal projection
  fixing the dilated state, with `Π P Π` the inflation of the compression of `P`.
* Leakage: the part `(1 - Π) P ψ'` of a dilated operator that leaves the ground
  slice is bounded by the intertwining defect of `P ⊗ 1` against any `1 ⊗ Q`,
  because `(1 - Π) ⊗ 1` annihilates `(1 ⊗ Q) ψ'`.  This is the estimate that
  replaces the `≈_δ`-preservation which Naimark dilation lacks in general
  (`references/ldt-paper/orthonormalization.tex:82-101`, blueprint
  `ex:easy-but-long`).

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Contractions and their action on states -/



















/-- An operator `K` with `Kᴴ K ≤ 1` does not increase norms. -/
theorem norm_applyOperatorToState_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hK : Kᴴ * K ≤ 1) (v : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState K v‖ ≤ ‖v‖ := by
  have h := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hK v
  have hv : (inner ℂ v v).re = ‖v‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [← _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_sq, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_one, hv] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h



/-- Orthogonal projections are contractions. -/
theorem conjTranspose_mul_le_one_of_isProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hP : _root_.LIDT.MIPStarRE.Quantum.IsProj P) : Pᴴ * P ≤ 1 := by
  have hstar : Pᴴ = P := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hP.isSelfAdjoint.star_eq
  rw [hstar, hP.isIdempotentElem.eq]
  exact sub_nonneg.mp hP.one_sub.nonneg











/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/









/-! ## Matrices of isometries -/





















/-! ## The ground projection -/





















/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/





end

end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Upstream.lean. -/
/-!
# Public helpers for the upstream LIDT interface

These finite-sum and measurement lemmas support the QPBT without modifying its LIDT dependency.
The marginal-state construction and rank-zero argument adapt the private proofs in
`LionSR/MIPStarRE`, commit `f382c801026f53a9efc260fdee707cb35e0adb15`, module
`MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair`.
The remaining lemmas are QPBT extensions of the upstream measurement and distribution APIs.
Their proofs use the public definitions and Mathlib finite-dimensional linear algebra.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder



namespace LIDT
namespace MIPStarRE.LDT



/-- A uniform average over a finite type is its normalized finite sum. -/
theorem avgOver_uniform_eq_inv_card_mul_sum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) f = (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  unfold _root_.LIDT.MIPStarRE.LDT.avgOver _root_.LIDT.MIPStarRE.LDT.uniformDistribution _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset
  simp only [Finset.mem_univ, ite_true, Finset.card_univ, one_div, Finset.mul_sum]


end MIPStarRE.LDT
end LIDT

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
# Retained point mismatch from ordered estimates

The incorrect point projection is the outer factor of the ordered product.
The scalar collision identity then bounds its average image norm without an
outcome-count factor. All vectors remain unnormalized.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1360-1404`,
`eq:qld-s-good-and-bad` through `eq:qld-sgg-mhat-sandwich`;
blueprint `lem:qld-4-7`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.PolynomialImageBounds

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]

theorem solution (X Z : _root_.LIDT.MIPStarRE.Quantum.Measurement F ι)
    (hX : _root_.MIPStarRE.QPBT.Measurement.IsProjective X) (hZ : _root_.MIPStarRE.QPBT.Measurement.IsProjective Z)
    (r t : F) (ψ : EuclideanSpace ℂ ι) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) (fun v =>
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState ((1 - X.effect r) *
        _root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)) ψ‖ ^ 2) ≤
      2 * (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 := by
  classical
  let w (bc : F × F) := _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
    (Z.effect bc.2 * X.effect bc.1 * Z.effect bc.2)
  have hw (bc : F × F) : 0 ≤ w bc :=
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg ψ ((_root_.MIPStarRE.QPBT.pastedMeasurement_isMeasurement X Z hZ).1 bc)
  have hsum : ∑ bc, w bc = ‖ψ‖ ^ 2 := by
    rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_one ψ, ← (_root_.MIPStarRE.QPBT.pastedMeasurement_isMeasurement X Z hZ).2,
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
    rfl
  have hpoint (v : Fin 2 → F) :
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState ((1 - X.effect r) *
        _root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)) ψ‖ ^ 2 ≤
      (if v 1 = 0 then ‖ψ‖ ^ 2 else 0) + ∑ bc : F × F,
        (if v 0 * bc.1 + v 1 * bc.2 = v 0 * r + v 1 * t ∧ bc.1 ≠ r
          then 1 else 0) * w bc := by
    by_cases hv : v 1 = 0
    · rw [if_pos hv]
      apply le_trans (b := ‖ψ‖ ^ 2)
      · apply pow_le_pow_left₀ (norm_nonneg _)
        rw [_root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
        exact (_root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_le
          (_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_of_isProj (hX r).one_sub) _).trans
          (_root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_le
            (_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator_gram_le_one X Z hX hZ _ _ _) ψ)
      · exact le_add_of_nonneg_right (Finset.sum_nonneg fun bc _ =>
          mul_nonneg (by split_ifs <;> norm_num) (hw bc))
    · rw [if_neg hv, zero_add, _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_sq]
      change _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ _ ≤ _
      rw [wrong_ordered_gram X Z hX r _ _ _ hv, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro bc _
      split_ifs <;> simp [w, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
  have hexc : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F))
      (fun v => if v 1 = 0 then ‖ψ‖ ^ 2 else 0) =
        (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 := by
    change _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F))
      (fun v => if ((finTwoArrowEquiv F) v).2 = 0 then ‖ψ‖ ^ 2 else 0) = _
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv (finTwoArrowEquiv F)]
    simp only [Equiv.apply_symm_apply]
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_snd (fun β : F => if β = 0 then ‖ψ‖ ^ 2 else 0)]
    simp [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_eq_inv_card_mul_sum]
  have hcollision (bc : F × F) :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) (fun v =>
        if v 0 * bc.1 + v 1 * bc.2 = v 0 * r + v 1 * t ∧ bc.1 ≠ r
          then (1 : ℝ) else 0) ≤ (Fintype.card F : ℝ)⁻¹ := by
    by_cases hb : bc.1 = r
    · simp [hb, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const]
    · rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv (finTwoArrowEquiv F)]
      have h := _root_.MIPStarRE.QPBT.affine_collision_average bc (r, t)
      have hne : bc ≠ (r, t) := fun h => hb (congrArg Prod.fst h)
      simpa [finTwoArrowEquiv, hb, hne] using h.le
  have h := _root_.LIDT.MIPStarRE.LDT.avgOver_mono (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) _ _ hpoint
  simp only [_root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_sum, _root_.LIDT.MIPStarRE.LDT.avgOver_mul_const, hexc] at h
  refine h.trans ?_
  have hc := Finset.sum_le_sum (s := Finset.univ) fun bc _ =>
    mul_le_mul_of_nonneg_right (hcollision bc) (hw bc)
  rw [← Finset.mul_sum, hsum] at hc
  linarith
