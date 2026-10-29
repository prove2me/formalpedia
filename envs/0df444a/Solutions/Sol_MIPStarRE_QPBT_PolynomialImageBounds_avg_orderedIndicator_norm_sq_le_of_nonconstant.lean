-- Prove2me | solution 1 for MIPStarRE.QPBT.PolynomialImageBounds.avg_orderedIndicator_norm_sq_le_of_nonconstant
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:53:00.340726+00:00
-- url     : https://prove2.me/submissions/4b63448b-72b7-4c86-af25-0eba7da8930a

-- Generated proof for MIPStarRE.QPBT.PolynomialImageBounds.avg_orderedIndicator_norm_sq_le_of_nonconstant.
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
import Definitions.Def_QPBT_QPBT_Combining_PolynomialImageBounds
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Pasting_Heterogeneous
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_PolynomialImageBounds_abs_orderedIndicator_norm_sq_sub_diagonal_le
import Theorems.Thm_MIPStarRE_QPBT_PolynomialImageBounds_avg_weighted_fiber_le
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

/- Source helpers from QPBT/Combining/PolynomialFiberBounds.lean. -/
/-!
# Common exceptional fibers for polynomial coefficients

A nonconstant polynomial in one block, with polynomial coefficients in a
second block, has a nonzero coefficient at a nonconstant monomial. Its zero set controls
all exceptional specializations simultaneously, independently of the outcome
of a measurement. The weights may depend on the fixed block but not on the
block being averaged.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1341-1358`,
especially `eq:qld-g-2`; support for blueprint `lem:qld-4-7`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.PolynomialImageBounds

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]







variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem avg_diagonalIndicator_linear_le
    (X Z : _root_.LIDT.MIPStarRE.Quantum.Measurement F ι) (hZ : _root_.MIPStarRE.QPBT.Measurement.IsProjective Z)
    (r t : F) (ψ : EuclideanSpace ℂ ι) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) (fun v =>
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t))) ≤
      (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 +
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (Z.effect t * X.effect r * Z.effect t) := by
  classical
  let w (bc : F × F) : ℝ := _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
    (Z.effect bc.2 * X.effect bc.1 * Z.effect bc.2)
  have hw (bc : F × F) : 0 ≤ w bc :=
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg ψ ((_root_.MIPStarRE.QPBT.pastedMeasurement_isMeasurement X Z hZ).1 bc)
  have hsum : ∑ bc, w bc = ‖ψ‖ ^ 2 := by
    rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_one ψ, ← (_root_.MIPStarRE.QPBT.pastedMeasurement_isMeasurement X Z hZ).2,
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
    rfl
  have hexpand (v : Fin 2 → F) :
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator X Z (v 0) (v 1) (v 0 * r + v 1 * t)) =
      ∑ bc : F × F, (if v 0 * bc.1 + v 1 * bc.2 = v 0 * r + v 1 * t
        then 1 else 0) * w bc := by
    rw [_root_.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
    apply Finset.sum_congr rfl
    intro bc _
    split_ifs <;> simp [w, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
  have hcollision (bc : F × F) :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) (fun v =>
        if v 0 * bc.1 + v 1 * bc.2 = v 0 * r + v 1 * t then (1 : ℝ) else 0) =
        if bc = (r, t) then 1 else (Fintype.card F : ℝ)⁻¹ := by
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv (finTwoArrowEquiv F)]
    exact _root_.MIPStarRE.QPBT.affine_collision_average bc (r, t)
  simp_rw [hexpand, _root_.LIDT.MIPStarRE.LDT.avgOver_sum, _root_.LIDT.MIPStarRE.LDT.avgOver_mul_const, hcollision]
  calc
    _ ≤ ∑ bc : F × F, ((Fintype.card F : ℝ)⁻¹ +
        if bc = (r, t) then 1 else 0) * w bc := by
      apply Finset.sum_le_sum
      intro bc _
      apply mul_le_mul_of_nonneg_right _ (hw bc)
      split_ifs <;> simp
    _ = _ := by
      simp_rw [add_mul, Finset.sum_add_distrib]
      rw [← Finset.mul_sum, hsum]
      simp [w]

private theorem avg_orderedIndicator_linear_le
    (X Z : _root_.LIDT.MIPStarRE.Quantum.Measurement F ι) (hX : _root_.MIPStarRE.QPBT.Measurement.IsProjective X)
    (hZ : _root_.MIPStarRE.QPBT.Measurement.IsProjective Z) (r t : F) (ψ : EuclideanSpace ℂ ι) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) (fun v =>
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z (v 0) (v 1)
        (v 0 * r + v 1 * t)) ψ‖ ^ 2) ≤
      2 * (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 + _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (Z.effect t) := by
  have hexc : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F))
      (fun v => if v 1 = 0 then ‖ψ‖ ^ 2 else 0) =
        (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 := by
    change _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F))
      (fun v => if ((finTwoArrowEquiv F) v).2 = 0 then ‖ψ‖ ^ 2 else 0) = _
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv (finTwoArrowEquiv F)]
    simp only [Equiv.apply_symm_apply]
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_snd (fun β : F => if β = 0 then ‖ψ‖ ^ 2 else 0)]
    simp [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_eq_inv_card_mul_sum]
  have hdrop : _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (Z.effect t * X.effect r * Z.effect t) ≤
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (Z.effect t) := by
    apply _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono
    simpa only [Matrix.star_eq_conjTranspose, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian, mul_one,
      (hZ t).isIdempotentElem.eq] using
      star_left_conjugate_le_conjugate (_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_le_one X r) (Z.effect t)
  have havg := _root_.LIDT.MIPStarRE.LDT.avgOver_mono (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) _ _ (fun v =>
    le_trans (le_abs_self _) (_root_.MIPStarRE.QPBT.PolynomialImageBounds.abs_orderedIndicator_norm_sq_sub_diagonal_le
      X Z hX hZ (v 0) (v 1) (v 0 * r + v 1 * t) ψ))
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sub, hexc] at havg
  have hdiag := avg_diagonalIndicator_linear_le X Z hZ r t ψ
  linarith



end

end MIPStarRE.QPBT.PolynomialImageBounds

/-!
# Common exceptional fibers for polynomial coefficients

A nonconstant polynomial in one block, with polynomial coefficients in a
second block, has a nonzero coefficient at a nonconstant monomial. Its zero set controls
all exceptional specializations simultaneously, independently of the outcome
of a measurement. The weights may depend on the fixed block but not on the
block being averaged.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1341-1358`,
especially `eq:qld-g-2`; support for blueprint `lem:qld-4-7`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.PolynomialImageBounds

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]







variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution {n k C D : ℕ}
    (p : MvPolynomial (Fin n) (MvPolynomial (Fin k) F))
    (hp : ¬ ∃ r, p = MvPolynomial.C r)
    (hcoeff : ∀ e, (p.coeff e).totalDegree ≤ C) (hdegree : p.totalDegree ≤ D)
    (r : (Fin n → F) → (Fin k → F) → F)
    (X : (Fin n → F) → _root_.LIDT.MIPStarRE.Quantum.Measurement F ι)
    (Z : (Fin k → F) → _root_.LIDT.MIPStarRE.Quantum.Measurement F ι)
    (hX : ∀ x, _root_.MIPStarRE.QPBT.Measurement.IsProjective (X x))
    (hZ : ∀ z, _root_.MIPStarRE.QPBT.Measurement.IsProjective (Z z)) (ψ : EuclideanSpace ℂ ι) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin k → F)) (fun z =>
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F)) (fun x =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) (fun v =>
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator (X x) (Z z) (v 0) (v 1)
            (v 0 * r x z + v 1 *
              MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p))) ψ‖ ^ 2))) ≤
      ((C + D + 2 : ℕ) : ℝ) / Fintype.card F * ‖ψ‖ ^ 2 := by
  classical
  let w (z : Fin k → F) (b : F) := _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((Z z).effect b)
  have hsum (z : Fin k → F) : ∑ b, w z b = ‖ψ‖ ^ 2 := by
    rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum, (Z z).sum_eq_one, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_one]
  have hfiber := _root_.MIPStarRE.QPBT.PolynomialImageBounds.avg_weighted_fiber_le p hp hcoeff hdegree w (‖ψ‖ ^ 2)
    (fun z b => _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg ψ ((Z z).pos b)) hsum
  have heval (z : Fin k → F) (x : Fin n → F) :
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((Z z).effect
        (MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p))) =
      ∑ b : F, (if MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p) = b
        then 1 else 0) * w z b := by
    simp [w]
  calc
    _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin k → F)) (fun z =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F)) (fun x =>
          2 * (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 +
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((Z z).effect
            (MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p))))) := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
      intro z
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
      intro x
      exact avg_orderedIndicator_linear_le (X x) (Z z) (hX x) (hZ z) _ _ ψ
    _ = 2 * (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 +
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin k → F)) (fun z => ∑ b : F,
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F))
            (fun x => if MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p) = b
              then 1 else 0) * w z b) := by
      simp_rw [heval, _root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const, _root_.LIDT.MIPStarRE.LDT.avgOver_sum, _root_.LIDT.MIPStarRE.LDT.avgOver_mul_const]
    _ ≤ 2 * (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 +
        ((C + D : ℕ) : ℝ) / Fintype.card F * ‖ψ‖ ^ 2 := add_le_add le_rfl hfiber
    _ = _ := by push_cast; ring
