-- Prove2me | solution 1 for MIPStarRE.QPBT.PolynomialImageBounds.nonlinear_mass_le_ordered_error
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:53:00.218613+00:00
-- url     : https://prove2.me/submissions/11373526-181a-4b4c-b114-528f55861e12

-- Generated proof for MIPStarRE.QPBT.PolynomialImageBounds.nonlinear_mass_le_ordered_error.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Combining_PolynomialImageBounds
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Pasting_Heterogeneous
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_PolynomialImageBounds_abs_orderedIndicator_norm_sq_sub_diagonal_le

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



















/-- A polynomial not of the form `alpha * u + beta * v` has a nonzero
coefficient outside those two monomials. Applied over the ring of base-point
polynomials, this chooses one coefficient independently of both measurement
outcomes in the argument following `eq:qld-g-prime`. -/
private theorem exists_nonzero_nonlinear_coeff {R : Type*} [CommRing R]
    (p : MvPolynomial (Fin 2) R)
    (hp : ¬ ∃ u v : R, p = MvPolynomial.C u * MvPolynomial.X 0 +
      MvPolynomial.C v * MvPolynomial.X 1) :
    ∃ e : Fin 2 →₀ ℕ, e ≠ Finsupp.single 0 1 ∧ e ≠ Finsupp.single 1 1 ∧
      p.coeff e ≠ 0 := by
  classical
  have h01 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro h
    simpa using congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  by_contra! h
  apply hp
  refine ⟨p.coeff (Finsupp.single 0 1), p.coeff (Finsupp.single 1 1), ?_⟩
  ext e
  by_cases h0 : e = Finsupp.single 0 1
  · subst e
    simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, Ne.symm h01]
  · by_cases h1 : e = Finsupp.single 1 1
    · subst e
      simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, h01]
    · simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, Ne.symm h0, Ne.symm h1,
        h e h0 h1]

omit [Fintype F] [DecidableEq F] in
/-- A nonzero specialized coefficient outside the scalar-linear monomials
certifies nonzero difference from every `alpha * b + beta * c` simultaneously.
This is the common good-base-point criterion needed before sandwich weighting. -/
private theorem specialization_ne_linear_of_coeff {n : ℕ}
    (p : MvPolynomial (Fin 2) (MvPolynomial (Fin n) F)) (e : Fin 2 →₀ ℕ)
    (he0 : e ≠ Finsupp.single 0 1) (he1 : e ≠ Finsupp.single 1 1)
    (u : Fin n → F) (hu : MvPolynomial.eval u (p.coeff e) ≠ 0) (b c : F) :
    MvPolynomial.map (MvPolynomial.eval u) p ≠
      MvPolynomial.C b * MvPolynomial.X 0 + MvPolynomial.C c * MvPolynomial.X 1 := by
  intro h
  apply hu
  have hc := congrArg (fun p => p.coeff e) h
  simpa [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X,
    Ne.symm he0, Ne.symm he1] using hc

/-- Schwartz--Zippel in the uniform-average notation used by the coefficient
and fiber calculations in `eq:qld-g-prime-bound` and `eq:qld-g-2`. -/
theorem avg_eval_eq_le {n D : ℕ} (p r : MvPolynomial (Fin n) F)
    (hne : p ≠ r) (hp : p.totalDegree ≤ D) (hr : r.totalDegree ≤ D) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F))
      (fun u => if MvPolynomial.eval u p = MvPolynomial.eval u r then 1 else 0) ≤
      (D : ℝ) / Fintype.card F := by
  have hsz := _root_.LIDT.MIPStarRE.LDT.Preliminaries.schwartzZippel_totalDegree hne hp hr
  calc
    _ = (_root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability n F p r : ℝ) := by
      simp [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_eq_inv_card_mul_sum,
        _root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability, div_eq_mul_inv, mul_comm]
    _ ≤ (((D : ℚ≥0) / Fintype.card F : ℚ≥0) : ℝ) := by exact_mod_cast hsz
    _ = _ := by simp

/-- On every base point where the selected coefficient remains nonzero,
Schwartz--Zippel bounds agreement with each linear answer polynomial. The
bound is derived from coefficient polynomials, not assumed as a collision law. -/
private theorem avg_specialization_eq_linear_le_of_coeff {n : ℕ}
    (p : MvPolynomial (Fin 2) (MvPolynomial (Fin n) F)) (e : Fin 2 →₀ ℕ)
    (he0 : e ≠ Finsupp.single 0 1) (he1 : e ≠ Finsupp.single 1 1)
    (u : Fin n → F) (hu : MvPolynomial.eval u (p.coeff e) ≠ 0) (b c : F) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) (fun v =>
      if MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) p) =
        v 0 * b + v 1 * c then 1 else 0) ≤
      (max 1 p.totalDegree : ℕ) / (Fintype.card F : ℝ) := by
  have hdeg : (MvPolynomial.map (MvPolynomial.eval u) p).totalDegree ≤ p.totalDegree :=
    Finset.sup_mono (MvPolynomial.support_map_subset _ _)
  have hlin : (MvPolynomial.C b * MvPolynomial.X (0 : Fin 2) +
      MvPolynomial.C c * MvPolynomial.X (1 : Fin 2)).totalDegree ≤ 1 := by
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  simpa [mul_comm] using
    _root_.MIPStarRE.QPBT.PolynomialImageBounds.avg_eval_eq_le _ _ (specialization_ne_linear_of_coeff p e he0 he1 u hu b c)
      (hdeg.trans (le_max_right 1 _)) (hlin.trans (le_max_left 1 _))

/-- The first polynomial-image estimate for the diagonal sandwich, with
explicit degrees of the scalar polynomial and its base-point coefficients.
A single nonzero nonlinear coefficient supplies a common exceptional set for
all outcomes. Neither a uniform-collision premise nor an outcome-count loss
occurs. The nested polynomial ring is the coefficient expansion used at paper
lines 1311--1316; this theorem does not assert the later block-separation step. -/
private theorem avg_diagonalIndicator_le_of_not_linear {n : ℕ}
    (p : MvPolynomial (Fin 2) (MvPolynomial (Fin n) F))
    (hp : ¬ ∃ r s : MvPolynomial (Fin n) F,
      p = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1)
    (X Z : (Fin n → F) → _root_.LIDT.MIPStarRE.Quantum.Measurement F ι)
    (hZ : ∀ u, _root_.MIPStarRE.QPBT.Measurement.IsProjective (Z u)) (ψ : EuclideanSpace ℂ ι) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F)) (fun u =>
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) (fun v =>
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator (X u) (Z u) (v 0) (v 1)
          (MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) p))))) ≤
      ((p.support.sup fun e => (p.coeff e).totalDegree) + max 1 p.totalDegree : ℕ) /
        (Fintype.card F : ℝ) * ‖ψ‖ ^ 2 := by
  classical
  obtain ⟨e, he0, he1, he⟩ := exists_nonzero_nonlinear_coeff p hp
  let D : ℕ := p.support.sup fun e => (p.coeff e).totalDegree
  let E : ℝ := (max 1 p.totalDegree : ℕ) / (Fintype.card F : ℝ)
  let w (u : Fin n → F) (bc : F × F) : ℝ :=
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((Z u).effect bc.2 * (X u).effect bc.1 * (Z u).effect bc.2)
  let f (u : Fin n → F) (v : Fin 2 → F) : F :=
    MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) p)
  have hw (u : Fin n → F) (bc : F × F) : 0 ≤ w u bc :=
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg ψ ((_root_.MIPStarRE.QPBT.pastedMeasurement_isMeasurement (X u) (Z u) (hZ u)).1 bc)
  have hsum (u : Fin n → F) : ∑ bc : F × F, w u bc = ‖ψ‖ ^ 2 := by
    rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_one ψ,
      ← (_root_.MIPStarRE.QPBT.pastedMeasurement_isMeasurement (X u) (Z u) (hZ u)).2, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
    rfl
  have hexpand (u : Fin n → F) (v : Fin 2 → F) :
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator (X u) (Z u) (v 0) (v 1) (f u v)) =
        ∑ bc : F × F, (if f u v = v 0 * bc.1 + v 1 * bc.2 then 1 else 0) * w u bc := by
    rw [_root_.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
    refine Finset.sum_congr rfl fun bc _ => ?_
    by_cases h : f u v = v 0 * bc.1 + v 1 * bc.2
    · simp [h, w]
    · simp [Ne.symm h, h, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
  have hgood (u : Fin n → F) (hu : MvPolynomial.eval u (p.coeff e) ≠ 0) :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) (fun v =>
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator (X u) (Z u) (v 0) (v 1) (f u v))) ≤
        E * ‖ψ‖ ^ 2 := by
    simp_rw [hexpand, _root_.LIDT.MIPStarRE.LDT.avgOver_sum, _root_.LIDT.MIPStarRE.LDT.avgOver_mul_const]
    rw [← hsum u, Finset.mul_sum]
    exact Finset.sum_le_sum fun bc _ => mul_le_mul_of_nonneg_right
      (avg_specialization_eq_linear_le_of_coeff p e he0 he1 u hu bc.1 bc.2) (hw u bc)
  have hpoint (u : Fin n → F) :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) (fun v =>
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator (X u) (Z u) (v 0) (v 1) (f u v))) ≤
        (if MvPolynomial.eval u (p.coeff e) = 0 then 1 else 0) * ‖ψ‖ ^ 2 + E * ‖ψ‖ ^ 2 := by
    by_cases hu : MvPolynomial.eval u (p.coeff e) = 0
    · simp only [hu, if_true, one_mul]
      apply le_trans (b := ‖ψ‖ ^ 2)
      · apply _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_le_const
        intro v
        rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_one ψ]
        exact _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono (diagonalIndicator_bounds (X u) (Z u) (hZ u) _ _ _).2 ψ
      · exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))
    · simpa only [hu, if_false, zero_mul, zero_add] using hgood u hu
  have hbad : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F))
      (fun u => if MvPolynomial.eval u (p.coeff e) = 0 then 1 else 0) ≤
        (D : ℝ) / Fintype.card F := by
    simpa using _root_.MIPStarRE.QPBT.PolynomialImageBounds.avg_eval_eq_le (p.coeff e) 0 he
      (Finset.le_sup (f := fun j => (p.coeff j).totalDegree)
        (MvPolynomial.mem_support_iff.mpr he)) (by simp)
  calc
    _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F)) (fun u =>
        (if MvPolynomial.eval u (p.coeff e) = 0 then 1 else 0) * ‖ψ‖ ^ 2 + E * ‖ψ‖ ^ 2) :=
      _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ hpoint
    _ ≤ (D : ℝ) / Fintype.card F * ‖ψ‖ ^ 2 + E * ‖ψ‖ ^ 2 := by
      rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_mul_const, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const]
      exact add_le_add (mul_le_mul_of_nonneg_right hbad (sq_nonneg _)) le_rfl
    _ = _ := by dsimp [D, E]; push_cast; ring

/-- Adding the genuinely uniform zero-coefficient contribution gives the
ordered-product estimate for a polynomial outside the scalar-linear image.
The right side retains the squared norm of the unnormalized state. -/
private theorem avg_orderedIndicator_norm_sq_le_of_not_linear {n : ℕ}
    (p : MvPolynomial (Fin 2) (MvPolynomial (Fin n) F))
    (hp : ¬ ∃ r s : MvPolynomial (Fin n) F,
      p = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1)
    (X Z : (Fin n → F) → _root_.LIDT.MIPStarRE.Quantum.Measurement F ι)
    (hX : ∀ u, _root_.MIPStarRE.QPBT.Measurement.IsProjective (X u))
    (hZ : ∀ u, _root_.MIPStarRE.QPBT.Measurement.IsProjective (Z u)) (ψ : EuclideanSpace ℂ ι) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F)) (fun u =>
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) (fun v =>
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator (X u) (Z u) (v 0) (v 1)
          (MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) p))) ψ‖ ^ 2)) ≤
      ((p.support.sup fun e => (p.coeff e).totalDegree) + max 1 p.totalDegree + 1 : ℕ) /
        (Fintype.card F : ℝ) * ‖ψ‖ ^ 2 := by
  let f (u : Fin n → F) (v : Fin 2 → F) : F :=
    MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) p)
  have hexc : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F))
      (fun v => if v 1 = 0 then ‖ψ‖ ^ 2 else 0) =
        (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 := by
    change _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F))
      (fun v => if ((finTwoArrowEquiv F) v).2 = 0 then ‖ψ‖ ^ 2 else 0) = _
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv (finTwoArrowEquiv F)]
    simp only [Equiv.apply_symm_apply]
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_snd (fun β : F => if β = 0 then ‖ψ‖ ^ 2 else 0)]
    simp [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_eq_inv_card_mul_sum]
  calc
    _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F)) (fun u =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) (fun v =>
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator (X u) (Z u) (v 0) (v 1) (f u v)) +
            (if v 1 = 0 then ‖ψ‖ ^ 2 else 0))) := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
      intro u
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
      intro v
      have habs := _root_.MIPStarRE.QPBT.PolynomialImageBounds.abs_orderedIndicator_norm_sq_sub_diagonal_le
        (X u) (Z u) (hX u) (hZ u) (v 0) (v 1) (f u v) ψ
      have hle := le_trans (le_abs_self _) habs
      linarith
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F)) (fun u =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) (fun v =>
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator (X u) (Z u) (v 0) (v 1) (f u v)))) +
            (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 := by
      simp_rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add, hexc, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const]
    _ ≤ ((p.support.sup fun e => (p.coeff e).totalDegree) + max 1 p.totalDegree : ℕ) /
        (Fintype.card F : ℝ) * ‖ψ‖ ^ 2 + (Fintype.card F : ℝ)⁻¹ * ‖ψ‖ ^ 2 :=
      add_le_add (avg_diagonalIndicator_le_of_not_linear p hp X Z hZ ψ) le_rfl
    _ = _ := by push_cast; ring

/-- The ordered polynomial estimate sums over any specified set of polynomial
labels outside the scalar-linear image. Each label is weighted by its actual
state mass; the estimate never replaces a sum by the number of labels. -/
private theorem avg_sum_orderedIndicator_norm_sq_le_of_not_linear {n : ℕ} {Γ : Type*}
    (s : Finset Γ) (p : Γ → MvPolynomial (Fin 2) (MvPolynomial (Fin n) F))
    (hp : ∀ g ∈ s, ¬ ∃ r t : MvPolynomial (Fin n) F,
      p g = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1)
    (X Z : (Fin n → F) → _root_.LIDT.MIPStarRE.Quantum.Measurement F ι)
    (hX : ∀ u, _root_.MIPStarRE.QPBT.Measurement.IsProjective (X u))
    (hZ : ∀ u, _root_.MIPStarRE.QPBT.Measurement.IsProjective (Z u)) (ψ : Γ → EuclideanSpace ℂ ι) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F)) (fun u =>
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) (fun v => ∑ g ∈ s,
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator (X u) (Z u) (v 0) (v 1)
          (MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) (p g)))) (ψ g)‖ ^ 2)) ≤
      ∑ g ∈ s,
        (((p g).support.sup fun e => ((p g).coeff e).totalDegree) +
          max 1 (p g).totalDegree + 1 : ℕ) / (Fintype.card F : ℝ) * ‖ψ g‖ ^ 2 := by
  simp_rw [_root_.LIDT.MIPStarRE.LDT.avgOver_finset_sum]
  exact Finset.sum_le_sum fun g hg =>
    avg_orderedIndicator_norm_sq_le_of_not_linear (p g) (hp g hg) X Z hX hZ (ψ g)

omit [DecidableEq ι] in
/-- The squared-norm triangle inequality retains each outcome's state vector.
This norm-to-residual step is shared with the
wrong-variable argument in `eq:qld-g-prime-xpt-bound`; support for blueprint
`lem:qld-4-7`. No normalization is assumed. -/
theorem sum_mass_le_residual_add_image {Γ : Type*} (s : Finset Γ)
    (ψ A : Γ → EuclideanSpace ℂ ι) :
    ∑ g ∈ s, ‖ψ g‖ ^ 2 ≤
      2 * ∑ g ∈ s, ‖ψ g - A g‖ ^ 2 + 2 * ∑ g ∈ s, ‖A g‖ ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun g _ => ?_
  have htriangle := norm_add_le (ψ g - A g) (A g)
  rw [sub_add_cancel] at htriangle
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  nlinarith [sq_nonneg (‖ψ g - A g‖ - ‖A g‖)]



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

theorem solution {n : ℕ} {Γ : Type*}
    (s : Finset Γ) (p : Γ → MvPolynomial (Fin 2) (MvPolynomial (Fin n) F))
    (hp : ∀ g ∈ s, ¬ ∃ r t : MvPolynomial (Fin n) F,
      p g = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1)
    (X Z : (Fin n → F) → _root_.LIDT.MIPStarRE.Quantum.Measurement F ι)
    (hX : ∀ u, _root_.MIPStarRE.QPBT.Measurement.IsProjective (X u))
    (hZ : ∀ u, _root_.MIPStarRE.QPBT.Measurement.IsProjective (Z u)) (ψ : Γ → EuclideanSpace ℂ ι) :
    ∑ g ∈ s, ‖ψ g‖ ^ 2 ≤
      2 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F)) (fun u =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) (fun v => ∑ g ∈ s,
          ‖ψ g - _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator (X u) (Z u) (v 0) (v 1)
            (MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) (p g)))) (ψ g)‖ ^ 2)) +
      2 * ∑ g ∈ s,
        (((p g).support.sup fun e => ((p g).coeff e).totalDegree) +
          max 1 (p g).totalDegree + 1 : ℕ) / (Fintype.card F : ℝ) * ‖ψ g‖ ^ 2 := by
  let A (u : Fin n → F) (v : Fin 2 → F) (g : Γ) : EuclideanSpace ℂ ι :=
    _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator (X u) (Z u) (v 0) (v 1)
      (MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) (p g)))) (ψ g)
  have hpoint (u : Fin n → F) (v : Fin 2 → F) :
      ∑ g ∈ s, ‖ψ g‖ ^ 2 ≤
        2 * ∑ g ∈ s, ‖ψ g - A u v g‖ ^ 2 + 2 * ∑ g ∈ s, ‖A u v g‖ ^ 2 :=
    _root_.MIPStarRE.QPBT.PolynomialImageBounds.sum_mass_le_residual_add_image s ψ (A u v)
  have havg := _root_.LIDT.MIPStarRE.LDT.avgOver_mono (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F)) _ _ fun u =>
    _root_.LIDT.MIPStarRE.LDT.avgOver_mono (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) _ _ (hpoint u)
  simp only [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const, _root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul] at havg
  have hnorm := avg_sum_orderedIndicator_norm_sq_le_of_not_linear s p hp X Z hX hZ ψ
  change ∑ g ∈ s, ‖ψ g‖ ^ 2 ≤ 2 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F))
    (fun u => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F))
      (fun v => ∑ g ∈ s, ‖ψ g - A u v g‖ ^ 2)) + _
  change _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F))
    (fun u => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin 2 → F))
      (fun v => ∑ g ∈ s, ‖A u v g‖ ^ 2)) ≤ _ at hnorm
  linarith
