-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Geometry.MetricGreenData.one_block_zero_of_variance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:38:50.785326+00:00
-- url     : https://prove2.me/submissions/9b621a16-7783-46c4-878d-e4ddf73fd06b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C018
import Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_MetricGreenData_preVarianceGreen_oriented
import Theorems.Thm_OAI_PositiveEinsteinFour_QuaternionFrame_arrayCoupledIntegrand_le_reduced
import Theorems.Thm_OAI_PositiveEinsteinFour_quadratic_form_nonneg_of_det
import Theorems.Thm_OAI_PositiveEinsteinFour_reduced_integrand_bound

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Bianchi
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete four-vector coordinates for a Bianchi gradient

The three quaternion actions are left multiplication by `i,j,k` on the real
four-dimensional Euclidean space. A symmetric matrix of four-vectors is
encoded by its three diagonal and three off-diagonal entries. Its divergence
constraint is the actual quaternionic Bianchi constraint of Section 2.
-/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators

theorem Tensor.matrix_symmetric (T : Tensor) (i j : Fin 3) :
    T.matrix i j = T.matrix j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem parameters_traceFree (S : Shape) (p k l : Vec) :
    (parameters S p k l).traceFree := by
  unfold Tensor.traceFree parameters
  simp only [Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [S.trace, difference_sum]
  simp

theorem parameters_bianchi (S : Shape) (p k l : Vec) :
    (parameters S p k l).bianchi := by
  rw [Tensor.bianchi_iff]
  intro i
  change S.s i • p - difference S.s i • k +
    (parameters S p k l).auxiliary (next i) - (parameters S p k l).auxiliary (previous i) = 0
  rw [parameters_auxiliary, parameters_auxiliary]
  calc
    _ = (S.s i + (difference S.s (next i) - difference S.s (previous i)) / 3) • p +
        (-difference S.s i + S.s (next i) - S.s (previous i)) • k := by module
    _ = 0 := by
      rw [S.difference_next_sub_previous]
      have hp : S.s i + -3 * S.s i / 3 = 0 := by ring
      have hk : -difference S.s i + S.s (next i) - S.s (previous i) = 0 := by
        unfold difference
        ring
      rw [hp, hk]
      simp

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Matrix
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small positive semidefinite forms and Schur completion

The closed determinant criterion includes vanishing diagonal entries. The
Schur estimate below consequently includes the singular axial endpoint of the
quadratic comparison in Section 6 of the manuscript.
-/

namespace PositiveEinsteinFour

/-- Conversely, nonnegativity of the binary form implies the closed diagonal
and determinant conditions. The singular diagonal case is tested directly. -/
theorem quadratic_form_det_of_nonneg
    (r h s : ℝ)
    (hform : ∀ x y, 0 ≤ r * x ^ 2 + 2 * s * x * y + h * y ^ 2) :
    0 ≤ r ∧ 0 ≤ h ∧ s ^ 2 ≤ r * h := by
  have hr : 0 ≤ r := by simpa using hform 1 0
  have hh : 0 ≤ h := by simpa using hform 0 1
  refine ⟨hr, hh, ?_⟩
  by_cases hrzero : r = 0
  · subst r
    have htest := hform (h + 1) (-s)
    have hhs : 0 ≤ h * s ^ 2 := mul_nonneg hh (sq_nonneg s)
    have hs : s = 0 := by nlinarith [sq_nonneg s]
    simp [hs]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrzero)
    have htest := hform (-s) r
    have hproduct : 0 ≤ r * (r * h - s ^ 2) := by nlinarith
    have hdet := nonneg_of_mul_nonneg_right hproduct hrpos
    linarith

end PositiveEinsteinFour

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_BianchiCurvature
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Curvature contractions of the concrete Bianchi tensor

The normalized spectral moments and the matrix-slot contraction are computed
from the actual symmetric matrix of Euclidean four-vectors in `Bianchi`.
-/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators

theorem Shape.rho_div_sqrt_three (S : Shape) : S.rho / Real.sqrt 3 = S.skewMoment := by
  unfold Shape.rho
  have hn : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp [hn]

/-- The normalized trace-free square is expanded in the two spectral vectors. -/
theorem Shape.square_decomposition (S : Shape) (i : Fin 3) :
    S.s i ^ 2 - 2 = S.sigma * S.s i + S.rho * S.tilde i := by
  have h := S.norm_coordinates
  have hr : S.rho * S.tilde i = S.skewMoment * difference S.s i := by
    unfold Shape.rho Shape.tilde
    have hn : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp [hn]
  rw [hr]
  unfold Shape.sigma Shape.skewMoment
  simp [Fin.sum_univ_succ, difference, next, previous]
  rw [S.trace_coordinates]
  fin_cases i
  · norm_num at *
    rw [S.trace_coordinates]
    linear_combination -(S.s 0 ^ 2 - 2 * S.s 0 * S.s 1 - 2 * S.s 1 ^ 2 - 6) / 9 * h
  · norm_num at *
    rw [S.trace_coordinates]
    linear_combination (2 * S.s 0 ^ 2 + 2 * S.s 0 * S.s 1 - S.s 1 ^ 2 + 6) / 9 * h
  · norm_num at *
    erw [S.trace_coordinates]
    linear_combination -(S.s 0 ^ 2 + 4 * S.s 0 * S.s 1 + S.s 1 ^ 2 - 6) / 9 * h

/-- Cubic moment in the unnormalized quarter-turn vector. -/
theorem Shape.mixed_cubic (S : Shape) :
    (∑ i, S.s i * difference S.s i ^ 2) = -18 * S.sigma := by
  unfold Shape.sigma
  simp [Fin.sum_univ_succ, difference, next, previous]
  rw [S.trace_coordinates]
  ring

private theorem diagonal_contraction (S : Shape) (p k l : Vec) :
    (∑ i, S.s i * ‖(parameters S p k l).diagonal i‖ ^ 2) =
      (∑ i, S.s i ^ 3) * ‖p‖ ^ 2 -
      2 * (∑ i, S.s i ^ 2 * difference S.s i) * inner ℝ p k +
      (∑ i, S.s i * difference S.s i ^ 2) * ‖k‖ ^ 2 := by
  change (∑ i, S.s i * ‖S.s i • p - difference S.s i • k‖ ^ 2) = _
  simp only [Fin.sum_univ_succ, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right]
  ring

private theorem off_contraction (S : Shape) (p k l : Vec) :
    (∑ i, S.s i * ‖(parameters S p k l).off i‖ ^ 2) =
      (∑ i, S.s i) * ‖l‖ ^ 2 + 2 * (∑ i, S.s i ^ 2) * inner ℝ l k +
      (2 / 3) * (∑ i, S.s i * difference S.s i) * inner ℝ l p +
      (∑ i, S.s i ^ 3) * ‖k‖ ^ 2 +
      (2 / 3) * (∑ i, S.s i ^ 2 * difference S.s i) * inner ℝ k p +
      (1 / 9) * (∑ i, S.s i * difference S.s i ^ 2) * ‖p‖ ^ 2 := by
  change (∑ i, S.s i * ‖-quaternion i (l + S.s i • k + (difference S.s i / 3) • p)‖ ^ 2) = _
  simp only [norm_neg, quaternion_norm, Fin.sum_univ_succ, norm_add_sq_real,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_add_left,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- The `B/v` matrix in Section 5 follows from the concrete parameter tensor.
All three variables remain real tangent four-vectors. -/
theorem curvatureContraction_parameters (S : Shape) (v : ℝ) (p k l : Vec) :
    curvatureContraction S v (parameters S p k l) =
      v * ((4 / 3) * S.sigma * ‖p‖ ^ 2 -
        8 * S.rho / Real.sqrt 3 * inner ℝ p k -
        4 * S.sigma * ‖k‖ ^ 2 - 2 * inner ℝ k l) := by
  unfold curvatureContraction
  rw [diagonal_contraction, off_contraction, S.trace, S.square,
    difference_orthogonal, S.mixed_cubic, real_inner_comm p k, real_inner_comm k l]
  have hc : (∑ i, S.s i ^ 3) = 6 * S.sigma := by unfold Shape.sigma; ring
  have hd : (∑ i, S.s i ^ 2 * difference S.s i) = 18 * S.skewMoment := by
    unfold Shape.skewMoment
    ring
  rw [hc, hd]
  have hr : 8 * S.rho / Real.sqrt 3 = 8 * S.skewMoment := by rw [mul_div_assoc, S.rho_div_sqrt_three]
  rw [hr]
  ring

/-- Rational form of the same trace-free square decomposition. -/
theorem Shape.squareWeight_eq (S : Shape) (i : Fin 3) :
    S.s i ^ 2 - 2 = S.sigma * S.s i + S.skewMoment * difference S.s i := by
  have h := S.square_decomposition i
  have hr : S.rho * S.tilde i = S.skewMoment * difference S.s i := by
    unfold Shape.rho Shape.tilde
    have hn : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp [hn]
  rwa [hr] at h

private theorem cube_sum (S : Shape) : (∑ i, S.s i ^ 3) = 6 * S.sigma := by
  unfold Shape.sigma
  ring

private theorem mixed_cube_sum (S : Shape) :
    (∑ i, S.s i ^ 2 * difference S.s i) = 18 * S.skewMoment := by
  unfold Shape.skewMoment
  ring

private theorem difference_cube_sum (S : Shape) :
    (∑ i, difference S.s i ^ 3) = -54 * S.skewMoment := by
  calc
    _ = -3 * ∑ i, S.s i ^ 2 * difference S.s i := by
      simp [difference, next, previous, Fin.sum_univ_succ]
      ring
    _ = _ := by rw [mixed_cube_sum]; ring

private theorem squareWeight_moments (S : Shape) :
    (∑ i, S.squareWeight i) = 0 ∧
    (∑ i, S.squareWeight i * S.s i) = 6 * S.sigma ∧
    (∑ i, S.squareWeight i * difference S.s i) = 18 * S.skewMoment ∧
    (∑ i, S.squareWeight i * S.s i ^ 2) = 6 ∧
    (∑ i, S.squareWeight i * S.s i * difference S.s i) = 0 ∧
    (∑ i, S.squareWeight i * difference S.s i ^ 2) = -18 := by
  have hsq : ∑ i, S.squareWeight i = 0 := by
    unfold Shape.squareWeight
    simp only [Finset.sum_sub_distrib, S.square, Finset.sum_const, Finset.card_fin]
    norm_num
  have hs : (∑ i, S.squareWeight i * S.s i) = 6 * S.sigma := by
    calc
      _ = (∑ i, S.s i ^ 3) - 2 * ∑ i, S.s i := by
        simp only [Shape.squareWeight, Fin.sum_univ_succ]
        ring
      _ = _ := by rw [cube_sum, S.trace]; ring
  have hd : (∑ i, S.squareWeight i * difference S.s i) = 18 * S.skewMoment := by
    calc
      _ = (∑ i, S.s i ^ 2 * difference S.s i) - 2 * ∑ i, difference S.s i := by
        simp only [Shape.squareWeight, Fin.sum_univ_succ]
        ring
      _ = _ := by rw [mixed_cube_sum, difference_sum]; ring
  have hs2 : (∑ i, S.squareWeight i * S.s i ^ 2) = 6 := by
    calc
      _ = S.sigma * (∑ i, S.s i ^ 3) +
          S.skewMoment * ∑ i, S.s i ^ 2 * difference S.s i := by
        simp_rw [Shape.squareWeight, S.squareWeight_eq]
        simp only [Fin.sum_univ_succ]
        ring
      _ = _ := by rw [cube_sum, mixed_cube_sum]; nlinarith [S.sigma_skew_circle]
  have hsd : (∑ i, S.squareWeight i * S.s i * difference S.s i) = 0 := by
    calc
      _ = S.sigma * (∑ i, S.s i ^ 2 * difference S.s i) +
          S.skewMoment * ∑ i, S.s i * difference S.s i ^ 2 := by
        simp_rw [Shape.squareWeight, S.squareWeight_eq]
        simp only [Fin.sum_univ_succ]
        ring
      _ = _ := by rw [mixed_cube_sum, S.mixed_cubic]; ring
  have hd2 : (∑ i, S.squareWeight i * difference S.s i ^ 2) = -18 := by
    calc
      _ = S.sigma * (∑ i, S.s i * difference S.s i ^ 2) +
          S.skewMoment * ∑ i, difference S.s i ^ 3 := by
        simp_rw [Shape.squareWeight, S.squareWeight_eq]
        simp only [Fin.sum_univ_succ]
        ring
      _ = _ := by rw [S.mixed_cubic, difference_cube_sum]; nlinarith [S.sigma_skew_circle]
  exact ⟨hsq, hs, hd, hs2, hsd, hd2⟩

private theorem weighted_diagonal_contraction
    (S : Shape) (w : Fin 3 → ℝ) (p k l : Vec) :
    (∑ i, w i * ‖(parameters S p k l).diagonal i‖ ^ 2) =
      (∑ i, w i * S.s i ^ 2) * ‖p‖ ^ 2 -
      2 * (∑ i, w i * S.s i * difference S.s i) * inner ℝ p k +
      (∑ i, w i * difference S.s i ^ 2) * ‖k‖ ^ 2 := by
  change (∑ i, w i * ‖S.s i • p - difference S.s i • k‖ ^ 2) = _
  simp only [Fin.sum_univ_succ, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right]
  ring

private theorem weighted_off_contraction
    (S : Shape) (w : Fin 3 → ℝ) (p k l : Vec) :
    (∑ i, w i * ‖(parameters S p k l).off i‖ ^ 2) =
      (∑ i, w i) * ‖l‖ ^ 2 + 2 * (∑ i, w i * S.s i) * inner ℝ l k +
      (2 / 3) * (∑ i, w i * difference S.s i) * inner ℝ l p +
      (∑ i, w i * S.s i ^ 2) * ‖k‖ ^ 2 +
      (2 / 3) * (∑ i, w i * S.s i * difference S.s i) * inner ℝ k p +
      (1 / 9) * (∑ i, w i * difference S.s i ^ 2) * ‖p‖ ^ 2 := by
  change (∑ i, w i * ‖-quaternion i (l + S.s i • k + (difference S.s i / 3) • p)‖ ^ 2) = _
  simp only [norm_neg, quaternion_norm, Fin.sum_univ_succ, norm_add_sq_real,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_add_left,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- The `C_N/v²` matrix in Section 5 from the concrete four-vector tensor. -/
theorem squareCurvatureContraction_parameters (S : Shape) (v : ℝ) (p k l : Vec) :
    squareCurvatureContraction S v (parameters S p k l) =
      v ^ 2 * ((4 / 3) * ‖p‖ ^ 2 - 2 * S.rho / Real.sqrt 3 * inner ℝ p l -
        4 * ‖k‖ ^ 2 - 2 * S.sigma * inner ℝ k l) := by
  obtain ⟨h0, hs, hd, hs2, hsd, hd2⟩ := squareWeight_moments S
  unfold squareCurvatureContraction
  rw [weighted_diagonal_contraction, weighted_off_contraction,
    h0, hs, hd, hs2, hsd, hd2, real_inner_comm p l, real_inner_comm k l]
  have hr : 2 * S.rho / Real.sqrt 3 = 2 * S.skewMoment := by rw [mul_div_assoc, S.rho_div_sqrt_three]
  rw [hr]
  ring

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_BianchiHessian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The Hessian matrix on actual quaternionic Bianchi tensors

The energy pairing and the matrix-slot operator are transported through the
proved bijective parametrization. Thus the squared-operator term uses the
inverse energy metric automatically.
-/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators

private theorem parameters_add_matrix (S : Shape) (p k l p' k' l' : Vec) (i j : Fin 3) :
    (parameters S (p + p') (k + k') (l + l')).matrix i j =
      (parameters S p k l).matrix i j + (parameters S p' k' l').matrix i j := by
  fin_cases i <;> fin_cases j <;> simp [Tensor.matrix, parameters] <;> module

/-- The full inner product, not just the norm, is transported by the coordinate
map with metric `diag(5/3,5,1)`. -/
theorem parameters_pairing (S : Shape) (p k l p' k' l' : Vec) :
    (parameters S p k l).pairing (parameters S p' k' l') =
      (5 / 3) * inner ℝ p p' + 5 * inner ℝ k k' + inner ℝ l l' := by
  have hn : (parameters S (p + p') (k + k') (l + l')).squaredNorm =
      (parameters S p k l).squaredNorm +
      2 * (∑ i, ∑ j, inner ℝ ((parameters S p k l).matrix i j)
        ((parameters S p' k' l').matrix i j)) + (parameters S p' k' l').squaredNorm := by
    unfold Tensor.squaredNorm
    simp_rw [parameters_add_matrix, norm_add_sq_real]
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have h0 := parameters_energy S (p + p') (k + k') (l + l')
  have h1 := parameters_energy S p k l
  have h2 := parameters_energy S p' k' l'
  simp only [norm_add_sq_real] at h0
  unfold Tensor.pairing
  linarith

/-- The transported operator is self-adjoint for the actual energy pairing. -/
theorem curvatureAction_pairing (S : Shape) (v : ℝ) (p k l p' k' l' : Vec) :
    (curvatureAction S v p k l).pairing (parameters S p' k' l') =
      v * ((4 / 3) * S.sigma * inner ℝ p p' -
        4 * S.skewMoment * (inner ℝ p k' + inner ℝ k p') -
        4 * S.sigma * inner ℝ k k' - inner ℝ k l' - inner ℝ l k') := by
  unfold curvatureAction
  rw [parameters_pairing]
  unfold curvatureActionP curvatureActionK curvatureActionL
  simp only [inner_sub_left, real_inner_smul_left]
  ring

/-- The `B H⁻¹ B` term is the squared Hilbert--Schmidt norm of the actual
transported operator, with all tangent correlations retained. -/
theorem curvatureAction_energy (S : Shape) (v : ℝ) (p k l : Vec) :
    (curvatureAction S v p k l).squaredNorm / 6 =
      v ^ 2 * ((16 / 15) * ‖p‖ ^ 2 + (21 / 5) * ‖k‖ ^ 2 + ‖l‖ ^ 2 / 5 +
        (8 / 5) * S.skewMoment * inner ℝ p l + (8 / 5) * S.sigma * inner ℝ k l) := by
  unfold curvatureAction
  rw [parameters_energy]
  unfold curvatureActionP curvatureActionK curvatureActionL
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_sub_sq_real,
    inner_sub_left, real_inner_smul_left, real_inner_smul_right]
  linear_combination
    v ^ 2 * ((16 / 15) * ‖p‖ ^ 2 + (16 / 5) * ‖k‖ ^ 2) * S.sigma_skew_circle

/-- Equation (12) on real tangent vectors, with the precise off-diagonal
pairings and without assumptions about their signs. -/
theorem hessianTensor_matrix (S : Shape) (v b : ℝ) (p k l : Vec) :
    hessianTensorForm S v b p k l =
      (-70 - 5 * b ^ 2 + 100 * S.sigma * v - 25 * v ^ 2) * ‖p‖ ^ 2 +
      (-210 - 15 * b ^ 2 - 300 * S.sigma * v - 190 * v ^ 2) * ‖k‖ ^ 2 +
      (-42 - 3 * b ^ 2 - 10 * v ^ 2) * ‖l‖ ^ 2 -
      200 * Real.sqrt 3 * S.rho * v * inner ℝ p k -
      70 * S.rho * v ^ 2 / Real.sqrt 3 * inner ℝ p l -
      2 * (75 * v + 35 * S.sigma * v ^ 2) * inner ℝ k l := by
  unfold hessianTensorForm
  rw [parameters_energy, curvatureContraction_parameters,
    squareCurvatureContraction_parameters, curvatureAction_energy]
  unfold Shape.rho
  have hs : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp [hn]
  ring_nf
  rw [hs]
  ring

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientPairing
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bilinear compression on the actual Bianchi gradient space. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

theorem rawPairing_comm (Z W : RawGradient) : rawPairing Z W = rawPairing W Z := by
  simp only [rawPairing, mul_comm]

theorem gradientCouplingKernel_symmetric (p q : GradientIndex) :
    gradientCouplingKernel p q = gradientCouplingKernel q p := by
  unfold gradientCouplingKernel
  apply Finset.sum_congr rfl
  intro s _
  rw [quaternionMatrix_skew s p.1 q.1,
    rotation_skew s p.2.1 q.2.1, rotation_skew s p.2.2 q.2.2]
  simp only [eq_comm (a := q.2.1) (b := p.2.1),
    eq_comm (a := q.2.2) (b := p.2.2)]
  split_ifs <;> ring

theorem rawCoupling_selfadjoint (Z W : RawGradient) :
    rawPairing (rawCoupling Z) W = rawPairing Z (rawCoupling W) := by
  simp only [rawPairing, rawCoupling_coordinates, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [gradientCouplingKernel_symmetric q p]
  ring

theorem rawPairing_smul_left (r : ℝ) (Z W : RawGradient) :
    rawPairing (r • Z) W = r * rawPairing Z W := by
  change (∑ p : GradientIndex, (r * rawCoordinates Z p) * rawCoordinates W p) = _
  simp only [mul_assoc, rawPairing, ← Finset.mul_sum]

theorem rawPairing_smul_right (r : ℝ) (Z W : RawGradient) :
    rawPairing Z (r • W) = r * rawPairing Z W := by
  change (∑ p : GradientIndex, rawCoordinates Z p * (r * rawCoordinates W p)) = _
  simp only [mul_left_comm, rawPairing, ← Finset.mul_sum]

theorem rawPairing_sub_left (Z W U : RawGradient) :
    rawPairing (Z - W) U = rawPairing Z U - rawPairing W U := by
  change (∑ p : GradientIndex,
    (rawCoordinates Z p - rawCoordinates W p) * rawCoordinates U p) = _
  simp only [sub_mul, rawPairing, Finset.sum_sub_distrib]

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_BianchiCurvatureProjection
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual matrix-slot curvature form and its Bianchi compression. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

/-- The coordinate pairing used for the raw commutator has the expected
normalization relative to the Bianchi energy metric. -/
theorem tensor_pairing_eq_raw (Z W : Tensor) :
    rawPairing Z.matrix W.matrix = 6 * Z.pairing W := by
  rw [rawPairing_vectors]
  unfold Tensor.pairing
  ring

/-- Matrix entries agree with the invariant trace-free anticommutator. -/
theorem matrixCurvatureTensor_matrix (S : Shape) (v : ℝ) (Z : Tensor)
    (a b : Fin 3) (j : Fin 4) :
    (matrixCurvatureTensor S v Z).matrix a b j =
      diagonalCurvatureAction (fun s => v * S.s s)
        (fun a b => Z.matrix a b j) a b := by
  have hs := S.trace_coordinates
  fin_cases a <;> fin_cases b <;>
    simp [matrixCurvatureTensor, diagonalCurvatureAction, Tensor.matrix,
      Fin.sum_univ_three, hs]
  all_goals first | (left; ring) | ring

/-- The trace correction vanishes when paired with a trace-free tensor. -/
theorem matrixCurvatureTensor_pairing (S : Shape) (v : ℝ) (Z W : Tensor)
    (hw : W.traceFree) :
    (matrixCurvatureTensor S v Z).pairing W = curvatureBilinear S v Z W := by
  have hzero : inner ℝ (∑ c, S.s c • Z.diagonal c) (∑ a, W.diagonal a) = 0 := by
    rw [hw, inner_zero_right]
  simp only [Fin.sum_univ_three, inner_add_right, inner_add_left,
    real_inner_smul_left] at hzero
  simp [Tensor.pairing, Tensor.matrix, matrixCurvatureTensor,
    curvatureBilinear, Fin.sum_univ_three, inner_sub_left,
    real_inner_smul_left]
  simp only [inner_add_left, real_inner_smul_left]
  linear_combination (-v / 18) * hzero

private theorem parameters_add_diagonal (S : Shape) (p k l p' k' l' : Vec)
    (a : Fin 3) :
    (parameters S (p + p') (k + k') (l + l')).diagonal a =
      (parameters S p k l).diagonal a + (parameters S p' k' l').diagonal a := by
  simp only [parameters, smul_add]
  module

private theorem parameters_add_off (S : Shape) (p k l p' k' l' : Vec)
    (a : Fin 3) :
    (parameters S (p + p') (k + k') (l + l')).off a =
      (parameters S p k l).off a + (parameters S p' k' l').off a := by
  simp only [parameters, smul_add, quaternion_add]
  module

/-- Polarization identifies the full operator, not only its quadratic form. -/
theorem curvatureAction_bilinear (S : Shape) (v : ℝ) (p k l p' k' l' : Vec) :
    (curvatureAction S v p k l).pairing (parameters S p' k' l') =
      curvatureBilinear S v (parameters S p k l) (parameters S p' k' l') := by
  have hpol : curvatureContraction S v (parameters S (p + p') (k + k') (l + l')) =
      curvatureContraction S v (parameters S p k l) +
        2 * curvatureBilinear S v (parameters S p k l) (parameters S p' k' l') +
          curvatureContraction S v (parameters S p' k' l') := by
    unfold curvatureContraction curvatureBilinear
    simp_rw [parameters_add_diagonal, parameters_add_off, norm_add_sq_real]
    simp only [Finset.sum_add_distrib, mul_add, Fin.sum_univ_three]
    ring
  rw [curvatureContraction_parameters, curvatureContraction_parameters,
    curvatureContraction_parameters] at hpol
  simp only [norm_add_sq_real, inner_add_left, inner_add_right,
    real_inner_comm] at hpol
  rw [curvatureAction_pairing]
  have hr := S.rho_div_sqrt_three
  rw [show 8 * S.rho / Real.sqrt 3 = 8 * S.skewMoment by
    rw [mul_div_assoc, hr]] at hpol
  linear_combination (1 / 2 : ℝ) * hpol

/-- The transported operator represents matrix-slot curvature against every
actual Bianchi gradient. This is the defining orthogonal compression property. -/
theorem curvatureAction_compression (S : Shape) (v : ℝ) (p k l : Vec)
    (W : Tensor) (hw : W.traceFree) (hb : W.bianchi) :
    (curvatureAction S v p k l).pairing W =
      (matrixCurvatureTensor S v (parameters S p k l)).pairing W := by
  rw [matrixCurvatureTensor_pairing S v _ W hw]
  rw [← parameters_reconstruction S W hw hb]
  exact curvatureAction_bilinear S v p k l _ _ _

/-- The square of the compressed operator is its pairing with the actual
uncompressed matrix action, so the energy formula is the required `E_B`. -/
theorem curvatureAction_compressed_energy (S : Shape) (v : ℝ) (p k l : Vec) :
    (matrixCurvatureTensor S v (parameters S p k l)).pairing
        (curvatureAction S v p k l) =
      (curvatureAction S v p k l).squaredNorm / 6 := by
  have h := curvatureAction_compression S v p k l (curvatureAction S v p k l)
    (parameters_traceFree S _ _ _) (parameters_bianchi S _ _ _)
  rw [← h]
  simp only [Tensor.pairing, Tensor.squaredNorm, real_inner_self_eq_norm_sq]

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Coupling
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Algebra and integration in the one-block vanishing argument

The scalar one-block vanishing argument in Section 8 of
*Positively curved Einstein four-manifolds* (23 September 2026). -/

namespace PositiveEinsteinFour

open MeasureTheory Filter

noncomputable section

theorem couplingCoefficient_lower {v b : ℝ}
    (hvb : v + b ≤ 2) (hv : 0 ≤ v) (hb : 0 ≤ b) :
    1 / 10 ≤ couplingCoefficient v b := by
  have hsum : (v + b) ^ 2 ≤ 4 := by nlinarith
  have hprod : v * b ≤ 1 := by nlinarith [sq_nonneg (v - b)]
  unfold couplingCoefficient
  nlinarith

theorem weight_denominator_pos {v : ℝ} (hv : 0 ≤ v) :
    0 < 1 + 6 * v + v ^ 2 := by positivity

theorem normWeight_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ normWeight v := by
  unfold normWeight
  positivity

/-- The fourth power identity supplies the sharp weight comparison. -/
theorem weight_defect_identity (z : ℝ) :
    1 + 6 * z ^ 2 + (z ^ 2) ^ 2 - 4 * z * (1 + z ^ 2) = (z - 1) ^ 4 := by
  ring

theorem normWeight_mul_sqrt_le {v : ℝ} (hv : 0 ≤ v) :
    normWeight v * Real.sqrt v ≤ 1 := by
  have hs := Real.sq_sqrt hv
  have hd := weight_denominator_pos hv
  have hid := weight_defect_identity (Real.sqrt v)
  rw [hs] at hid
  have hp : 0 ≤ (Real.sqrt v - 1) ^ 4 := by positivity
  unfold normWeight
  rw [div_mul_eq_mul_div]
  apply (div_le_one hd).2
  nlinarith [hid]

theorem normWeight_mul_sqrt_lt {v : ℝ} (hv : 0 ≤ v) (hne : v ≠ 1) :
    normWeight v * Real.sqrt v < 1 := by
  have hs := Real.sq_sqrt hv
  have hd := weight_denominator_pos hv
  have hz : Real.sqrt v - 1 ≠ 0 := by
    intro h
    have : Real.sqrt v = 1 := sub_eq_zero.mp h
    rw [this] at hs
    exact hne (by simpa using hs.symm)
  have hp : 0 < (Real.sqrt v - 1) ^ 4 := by positivity
  have hid := weight_defect_identity (Real.sqrt v)
  rw [hs] at hid
  unfold normWeight
  rw [div_mul_eq_mul_div]
  apply (div_lt_one hd).2
  nlinarith [hid]

theorem normWeight_le_inv_sqrt {v : ℝ} (hv : 0 < v) :
    normWeight v ≤ 1 / Real.sqrt v := by
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hv)).2
  exact normWeight_mul_sqrt_le hv.le

theorem normWeight_lt_inv_sqrt {v : ℝ} (hv : 0 < v) (hne : v ≠ 1) :
    normWeight v < 1 / Real.sqrt v := by
  apply (lt_div_iff₀ (Real.sqrt_pos.mpr hv)).2
  exact normWeight_mul_sqrt_lt hv.le hne

/-- Weighted two-term Cauchy--Schwarz, without any square-root denominators. -/
theorem weighted_square_le {a b s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (s * a + t * b) ^ 2 ≤ (a + b) * (s ^ 2 * a + t ^ 2 * b) := by
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (s - t))]

private theorem inv_sqrt_sq {v : ℝ} (hv : 0 ≤ v) :
    (1 / Real.sqrt v) ^ 2 = 1 / v := by
  rw [div_pow, one_pow, Real.sq_sqrt hv]

/-- Two-term Cauchy--Schwarz with the zero-denominator convention used in
the paper. The energies `p` and `q` stand for squared gradient norms. -/
theorem radial_cost_bound {v b p q : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpzero : v = 0 → p = 0) (hqzero : b = 0 → q = 0) :
    (normWeight v * p + normWeight b * q) ^ 2 ≤
      (p + q) * (p / v + q / b) := by
  have hpbound : normWeight v * p ≤ (1 / Real.sqrt v) * p := by
    rcases hv.eq_or_lt with hv | hv
    · simp [hpzero hv.symm]
    · exact mul_le_mul_of_nonneg_right (normWeight_le_inv_sqrt hv) hp
  have hqbound : normWeight b * q ≤ (1 / Real.sqrt b) * q := by
    rcases hb.eq_or_lt with hb | hb
    · simp [hqzero hb.symm]
    · exact mul_le_mul_of_nonneg_right (normWeight_le_inv_sqrt hb) hq
  have hr : 0 ≤ normWeight v * p + normWeight b * q :=
    add_nonneg (mul_nonneg (normWeight_nonneg hv) hp)
      (mul_nonneg (normWeight_nonneg hb) hq)
  have hsq := weighted_square_le (s := 1 / Real.sqrt v) (t := 1 / Real.sqrt b) hp hq
  rw [inv_sqrt_sq hv, inv_sqrt_sq hb] at hsq
  have hbound := add_le_add hpbound hqbound
  calc
    (normWeight v * p + normWeight b * q) ^ 2 ≤
        ((1 / Real.sqrt v) * p + (1 / Real.sqrt b) * q) ^ 2 := by nlinarith
    _ ≤ (p + q) * (p / v + q / b) := by simpa [div_eq_mul_inv, mul_comm] using hsq

theorem radial_cost_strict {v b p q : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpzero : v = 0 → p = 0) (hqzero : b = 0 → q = 0)
    (hactive : (0 < p ∧ v ≠ 1) ∨ (0 < q ∧ b ≠ 1)) :
    (normWeight v * p + normWeight b * q) ^ 2 <
      (p + q) * (p / v + q / b) := by
  have hpbound : normWeight v * p ≤ (1 / Real.sqrt v) * p := by
    rcases hv.eq_or_lt with hv | hv
    · simp [hpzero hv.symm]
    · exact mul_le_mul_of_nonneg_right (normWeight_le_inv_sqrt hv) hp
  have hqbound : normWeight b * q ≤ (1 / Real.sqrt b) * q := by
    rcases hb.eq_or_lt with hb | hb
    · simp [hqzero hb.symm]
    · exact mul_le_mul_of_nonneg_right (normWeight_le_inv_sqrt hb) hq
  have hbound : normWeight v * p + normWeight b * q <
      (1 / Real.sqrt v) * p + (1 / Real.sqrt b) * q := by
    rcases hactive with ⟨hpa, hne⟩ | ⟨hqa, hne⟩
    · have hvpos : 0 < v := lt_of_le_of_ne hv (by intro h; linarith [hpzero h.symm])
      exact add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_right (normWeight_lt_inv_sqrt hvpos hne) hpa) hqbound
    · have hbpos : 0 < b := lt_of_le_of_ne hb (by intro h; linarith [hqzero h.symm])
      exact add_lt_add_of_le_of_lt hpbound
        (mul_lt_mul_of_pos_right (normWeight_lt_inv_sqrt hbpos hne) hqa)
  have hr : 0 ≤ normWeight v * p + normWeight b * q :=
    add_nonneg (mul_nonneg (normWeight_nonneg hv) hp)
      (mul_nonneg (normWeight_nonneg hb) hq)
  have hsq := weighted_square_le (s := 1 / Real.sqrt v) (t := 1 / Real.sqrt b) hp hq
  rw [inv_sqrt_sq hv, inv_sqrt_sq hb] at hsq
  calc
    (normWeight v * p + normWeight b * q) ^ 2 <
        ((1 / Real.sqrt v) * p + (1 / Real.sqrt b) * q) ^ 2 := by nlinarith
    _ ≤ (p + q) * (p / v + q / b) := by simpa [div_eq_mul_inv, mul_comm] using hsq

/-- The final numerical contradiction once both nonzero norms are constant
and the published Weyl gaps have been applied. -/
theorem not_two_constant_blocks {v b : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hvGap : 1 ≤ v ^ 2) (hbGap : 1 ≤ b ^ 2) : ¬ v + b < 2 := by
  have hv1 : 1 ≤ v := by nlinarith
  have hb1 : 1 ≤ b := by nlinarith
  linarith

theorem coupled_square_identity {c θ r j : ℝ} (hc : c ≠ 0) :
    -c * j + 2 * θ * r - θ ^ 2 / c =
      -(θ - c * r) ^ 2 / c - c * (j - r ^ 2) := by
  field_simp
  ring

theorem coupled_nonpositive {c θ r j I : ℝ} (hc : 0 < c)
    (hj : r ^ 2 ≤ j) (hI : I ≤ -c * j + 2 * θ * r - θ ^ 2 / c) :
    I ≤ 0 := by
  rw [coupled_square_identity hc.ne'] at hI
  rw [neg_div] at hI
  have hsq : 0 ≤ (θ - c * r) ^ 2 / c := div_nonneg (sq_nonneg _) hc.le
  have hgap : 0 ≤ c * (j - r ^ 2) := mul_nonneg hc.le (sub_nonneg.mpr hj)
  linarith

theorem coupled_strictly_negative {c θ r j I : ℝ} (hc : 0 < c)
    (hj : r ^ 2 < j) (hI : I ≤ -c * j + 2 * θ * r - θ ^ 2 / c) :
    I < 0 := by
  rw [coupled_square_identity hc.ne'] at hI
  rw [neg_div] at hI
  have hsq : 0 ≤ (θ - c * r) ^ 2 / c := div_nonneg (sq_nonneg _) hc.le
  have hgap : 0 < c * (j - r ^ 2) := mul_pos hc (sub_pos.mpr hj)
  linarith

/-- The measure-theoretic closing step: a nonnegative integral forces equality
in the pointwise Cauchy--Schwarz bound. No integrability of the separate
possibly singular summands is needed here beyond integrability of `I`. -/
theorem ae_equality_of_coupled_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {I c θ r j : X → ℝ}
    (hIi : Integrable I μ) (hIntegral : 0 ≤ ∫ x, I x ∂μ)
    (hc : ∀ᵐ x ∂μ, 0 < c x) (hj : ∀ᵐ x ∂μ, r x ^ 2 ≤ j x)
    (hI : ∀ᵐ x ∂μ,
      I x ≤ -c x * j x + 2 * θ x * r x - θ x ^ 2 / c x) :
    ∀ᵐ x ∂μ, j x = r x ^ 2 := by
  have hnonpos : ∀ᵐ x ∂μ, I x ≤ 0 := by
    filter_upwards [hc, hj, hI] with x hcx hjx hIx
    exact coupled_nonpositive hcx hjx hIx
  have hint : ∫ x, I x ∂μ = 0 :=
    le_antisymm (integral_nonpos_of_ae hnonpos) hIntegral
  have hneg : ∀ᵐ x ∂μ, 0 ≤ -I x := by
    filter_upwards [hnonpos] with x hx using neg_nonneg.mpr hx
  have hzero : (fun x => -I x) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hneg hIi.neg).1 (by rw [integral_neg, hint, neg_zero])
  filter_upwards [hc, hj, hI, hzero] with x hcx hjx hIx hzx
  apply le_antisymm _ hjx
  by_contra h
  have hstrict := coupled_strictly_negative hcx (lt_of_not_ge h) hIx
  simp only [Pi.zero_apply, neg_eq_zero] at hzx
  linarith

/-- Equality in the radial bound annihilates both gradient energies. The
assumptions concerning level sets are exactly the scalar level-set fact used
in the manuscript, and are kept separate from the new coupled bound. -/
theorem zero_energies_of_radial_equality {v b p q : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpzero : v = 0 → p = 0) (hqzero : b = 0 → q = 0)
    (hpone : v = 1 → p = 0) (hqone : b = 1 → q = 0)
    (heq : (p + q) * (p / v + q / b) =
      (normWeight v * p + normWeight b * q) ^ 2) : p = 0 ∧ q = 0 := by
  by_contra h
  have hactive : (0 < p ∧ v ≠ 1) ∨ (0 < q ∧ b ≠ 1) := by
    by_cases hp0 : p = 0
    · right
      have hq0 : q ≠ 0 := by intro hq0; exact h ⟨hp0, hq0⟩
      refine ⟨lt_of_le_of_ne hq (Ne.symm hq0), ?_⟩
      intro hb1
      exact hq0 (hqone hb1)
    · left
      refine ⟨lt_of_le_of_ne hp (Ne.symm hp0), ?_⟩
      intro hv1
      exact hp0 (hpone hv1)
  have hlt := radial_cost_strict hv hb hp hq hpzero hqzero hactive
  linarith

/-- The first conclusion of the one-block vanishing argument, including zero
sets. The new geometric estimate on `I` is an explicit premise of this scalar
reduction, not an assumed published theorem or a claim that the geometric
estimate has already been proved. -/
theorem ae_zero_energies_of_coupled_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {I θ v b p q : X → ℝ}
    (hIi : Integrable I μ) (hIntegral : 0 ≤ ∫ x, I x ∂μ)
    (hv : ∀ᵐ x ∂μ, 0 ≤ v x) (hb : ∀ᵐ x ∂μ, 0 ≤ b x)
    (hsum : ∀ᵐ x ∂μ, v x + b x ≤ 2)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hsupport : ∀ᵐ x ∂μ,
      (v x = 0 → p x = 0) ∧ (b x = 0 → q x = 0) ∧
      (v x = 1 → p x = 0) ∧ (b x = 1 → q x = 0))
    (hI : ∀ᵐ x ∂μ,
      I x ≤ -couplingCoefficient (v x) (b x) *
        ((p x + q x) * (p x / v x + q x / b x)) +
        2 * θ x * (normWeight (v x) * p x + normWeight (b x) * q x) -
        θ x ^ 2 / couplingCoefficient (v x) (b x)) :
    ∀ᵐ x ∂μ, p x = 0 ∧ q x = 0 := by
  have hc : ∀ᵐ x ∂μ, 0 < couplingCoefficient (v x) (b x) := by
    filter_upwards [hv, hb, hsum] with x hvx hbx hsumx
    exact lt_of_lt_of_le (by norm_num) (couplingCoefficient_lower hsumx hvx hbx)
  have hj : ∀ᵐ x ∂μ,
      (normWeight (v x) * p x + normWeight (b x) * q x) ^ 2 ≤
        (p x + q x) * (p x / v x + q x / b x) := by
    filter_upwards [hv, hb, hp, hq, hsupport] with x hvx hbx hpx hqx hsx
    exact radial_cost_bound hvx hbx hpx hqx hsx.1 hsx.2.1
  have heq := ae_equality_of_coupled_bound hIi hIntegral hc hj hI
  filter_upwards [hv, hb, hp, hq, hsupport, heq] with x hvx hbx hpx hqx hsx heqx
  exact zero_energies_of_radial_equality hvx hbx hpx hqx
    hsx.1 hsx.2.1 hsx.2.2.1 hsx.2.2.2 heqx

/-- A variance bound turns a vanishing gradient energy into an almost-everywhere
constant. The mean is left explicit so the lemma does not require a particular
normalization of the measure. -/
theorem ae_eq_mean_of_zero_energy {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {v p : X → ℝ}
    (hi : Integrable (fun x => (v x - ∫ y, v y ∂μ) ^ 2) μ)
    (hvariance : (∫ x, (v x - ∫ y, v y ∂μ) ^ 2 ∂μ) ≤ ∫ x, p x ∂μ)
    (hp : p =ᵐ[μ] 0) : v =ᵐ[μ] fun _ => ∫ x, v x ∂μ := by
  have hpint : ∫ x, p x ∂μ = 0 := by rw [integral_congr_ae hp]; simp
  have hvarint : (∫ x, (v x - ∫ y, v y ∂μ) ^ 2 ∂μ) = 0 :=
    le_antisymm (by simpa only [hpint] using hvariance)
      (integral_nonneg fun _ => sq_nonneg _)
  have hzero := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).1 hvarint
  filter_upwards [hzero] with x hx
  simpa only [Pi.zero_apply, sq_eq_zero_iff, sub_eq_zero] using hx

/-- The full scalar one-block vanishing step of Section 8. The combined
integrand estimate is a premise, and remains a separate geometric obligation;
this theorem does not identify it as a published result. The variance and gap
premises have exactly the normalizations needed in the closing argument. -/
theorem one_block_vanishes_of_coupled_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {I θ v b p q : X → ℝ}
    (hIi : Integrable I μ) (hIntegral : 0 ≤ ∫ x, I x ∂μ)
    (hv : ∀ᵐ x ∂μ, 0 ≤ v x) (hb : ∀ᵐ x ∂μ, 0 ≤ b x)
    (hsum : ∀ᵐ x ∂μ, v x + b x < 2)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hsupport : ∀ᵐ x ∂μ,
      (v x = 0 → p x = 0) ∧ (b x = 0 → q x = 0) ∧
      (v x = 1 → p x = 0) ∧ (b x = 1 → q x = 0))
    (hI : ∀ᵐ x ∂μ,
      I x ≤ -couplingCoefficient (v x) (b x) *
        ((p x + q x) * (p x / v x + q x / b x)) +
        2 * θ x * (normWeight (v x) * p x + normWeight (b x) * q x) -
        θ x ^ 2 / couplingCoefficient (v x) (b x))
    (hvi : Integrable (fun x => (v x - ∫ y, v y ∂μ) ^ 2) μ)
    (hbi : Integrable (fun x => (b x - ∫ y, b y ∂μ) ^ 2) μ)
    (hvv : (∫ x, (v x - ∫ y, v y ∂μ) ^ 2 ∂μ) ≤ ∫ x, p x ∂μ)
    (hbv : (∫ x, (b x - ∫ y, b y ∂μ) ^ 2 ∂μ) ≤ ∫ x, q x ∂μ)
    (hvgap : (∃ x, v x ≠ 0) → 1 ≤ ∫ x, v x ^ 2 ∂μ)
    (hbgap : (∃ x, b x ≠ 0) → 1 ≤ ∫ x, b x ^ 2 ∂μ) :
    (∀ x, v x = 0) ∨ ∀ x, b x = 0 := by
  classical
  have hzero := ae_zero_energies_of_coupled_bound hIi hIntegral hv hb
    (hsum.mono fun _ hx => hx.le) hp hq hsupport hI
  have hvconst := ae_eq_mean_of_zero_energy hvi hvv (hzero.mono fun _ hx => hx.1)
  have hbconst := ae_eq_mean_of_zero_energy hbi hbv (hzero.mono fun _ hx => hx.2)
  by_contra hboth
  push Not at hboth
  have hvmean : 1 ≤ (∫ x, v x ∂μ) ^ 2 := by
    have hgap := hvgap hboth.1
    have heq : (∫ x, v x ^ 2 ∂μ) = (∫ x, v x ∂μ) ^ 2 := by
      calc
        _ = ∫ _ : X, (∫ x, v x ∂μ) ^ 2 ∂μ :=
          integral_congr_ae (hvconst.mono fun _ hx => congrArg (fun z : ℝ => z ^ 2) hx)
        _ = _ := by simp
    rwa [heq] at hgap
  have hbmean : 1 ≤ (∫ x, b x ∂μ) ^ 2 := by
    have hgap := hbgap hboth.2
    have heq : (∫ x, b x ^ 2 ∂μ) = (∫ x, b x ∂μ) ^ 2 := by
      calc
        _ = ∫ _ : X, (∫ x, b x ∂μ) ^ 2 ∂μ :=
          integral_congr_ae (hbconst.mono fun _ hx => congrArg (fun z : ℝ => z ^ 2) hx)
        _ = _ := by simp
    rwa [heq] at hgap
  obtain ⟨x, hx⟩ := (hv.and (hb.and (hsum.and (hvconst.and hbconst)))).exists
  dsimp only at hx
  have hvnonneg : 0 ≤ ∫ x, v x ∂μ := by rw [← hx.2.2.2.1]; exact hx.1
  have hbnonneg : 0 ≤ ∫ x, b x ∂μ := by rw [← hx.2.2.2.2]; exact hx.2.1
  have hstrict : (∫ x, v x ∂μ) + (∫ x, b x ∂μ) < 2 := by
    rw [← hx.2.2.2.1, ← hx.2.2.2.2]
    exact hx.2.2.1
  exact not_two_constant_blocks hvnonneg hbnonneg hvmean hbmean hstrict

end

end PositiveEinsteinFour

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MatrixSlotOperator
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_3 _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The varying matrix-slot curvature coefficient as an actual bounded
operator. The extension to all matrix arrays is self-adjoint; on trace-free
arrays it is the trace-free anticommutator used in the Weyl equation. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian Bianchi

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instNormedAddCommGroupMat
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instNormedSpaceRealMat
theorem matrixSlotAction_diagonal (t : Fin 3 → ℝ) (M : Mat) :
    matrixSlotAction (Matrix.diagonal t) M = diagonalCurvatureAction t M := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [matrixSlotAction, diagonalCurvatureAction, Matrix.diagonal,
      Fin.sum_univ_three]
  all_goals ring

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Variance
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted Poisson argument and the scalar weight used to balance the
Weyl moments. The Bochner and Poisson identities imply the exact bound for the test
function, including zero norm values. -/

namespace PositiveEinsteinFour.Variance

open MeasureTheory Filter

noncomputable section

/-- An integral version of the closed two-by-two determinant criterion.
It needs no square-root integrability assumptions. -/
theorem integral_pairing_sq_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g c : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hc : Integrable c μ)
    (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω) (hg0 : ∀ᵐ ω ∂μ, 0 ≤ g ω)
    (hpoint : ∀ᵐ ω ∂μ, c ω ^ 2 ≤ f ω * g ω) :
    (∫ ω, c ω ∂μ) ^ 2 ≤ (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ := by
  apply (quadratic_form_det_of_nonneg _ _ _ ?_).2.2
  intro x y
  have hnonneg : 0 ≤ ∫ ω, f ω * x ^ 2 + 2 * c ω * x * y + g ω * y ^ 2 ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hf0, hg0, hpoint] with ω hfω hgω hcω
    exact quadratic_form_nonneg_of_det _ _ _ hfω hgω hcω x y
  have h1 := integral_add ((hf.mul_const (x ^ 2)).add
    (((hc.const_mul 2).mul_const x).mul_const y)) (hg.mul_const (y ^ 2))
  have h2 := integral_add (hf.mul_const (x ^ 2))
    (((hc.const_mul 2).mul_const x).mul_const y)
  simp only [Pi.add_apply] at h1
  rw [h1, h2] at hnonneg
  simpa only [integral_mul_const, integral_const_mul] using hnonneg

end

end PositiveEinsteinFour.Variance

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_QuaternionGenerators
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rotation of the matrix indices is recovered from the actual
quaternion commutator.  Thus a four-dimensional quaternion lift also
intertwines the three-dimensional infinitesimal rotation generators. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem imaginaryLeft_entry (u : Fin 3 → ℝ) (r : Fin 3) :
    imaginaryCombination quaternionMatrix u r.succ 0 = u r := by
  rw [imaginaryCombination_apply]
  fin_cases r <;> simp [quaternionMatrix, Fin.sum_univ_three] <;> norm_num <;> rfl

theorem imaginaryLeft_injective :
    Function.Injective (imaginaryCombination quaternionMatrix) := by
  intro u v huv
  funext r
  simpa only [imaginaryLeft_entry] using
    congrArg (fun M : Mat4 => M r.succ 0) huv

theorem imaginaryLeft_general_commutator (u v : Fin 3 → ℝ) :
    imaginaryCombination quaternionMatrix u * imaginaryCombination quaternionMatrix v -
      imaginaryCombination quaternionMatrix v * imaginaryCombination quaternionMatrix u =
        imaginaryCombination quaternionMatrix
          ((∑ r, u r • TraceHessian.rotation r) *ᵥ v) := by
  calc
    _ = ∑ r, u r • (quaternionMatrix r * imaginaryCombination quaternionMatrix v -
          imaginaryCombination quaternionMatrix v * quaternionMatrix r) := by
      have hlinear (V : Mat4) :
          (∑ r, u r • quaternionMatrix r) * V - V * (∑ r, u r • quaternionMatrix r) =
            ∑ r, u r • (quaternionMatrix r * V - V * quaternionMatrix r) := by
        simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
          Matrix.mul_smul, smul_sub, Finset.sum_sub_distrib]
      exact hlinear _
    _ = ∑ r, u r • imaginaryCombination quaternionMatrix
        (TraceHessian.rotation r *ᵥ v) := by simp_rw [imaginaryLeft_commutator]
    _ = _ := by
      simp only [imaginaryCombination, Matrix.sum_mulVec, Matrix.smul_mulVec,
        Finset.sum_apply, Pi.smul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
      change (∑ r, ∑ s, (u r * (TraceHessian.rotation r *ᵥ v) s) • quaternionMatrix s) =
        ∑ s, ∑ r, (u r * (TraceHessian.rotation r *ᵥ v) s) • quaternionMatrix s
      exact Finset.sum_comm

/-- The matrix rotation generators transform under exactly the same
three-dimensional frame change as the imaginary quaternion basis. -/
theorem QuaternionLift.rotation_intertwines {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R) (s : Fin 3) :
    R * TraceHessian.rotation s =
      (∑ r, R r s • TraceHessian.rotation r) * R := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  apply imaginaryLeft_injective
  have hc := imaginaryLeft_general_commutator (fun r => R r s) (R *ᵥ v)
  have hl := imaginaryLeft_commutator s v
  have hv := intertwines_combination quaternionMatrix R P.matrix P.intertwines v
  have hw := intertwines_combination quaternionMatrix R P.matrix P.intertwines
    (TraceHessian.rotation s *ᵥ v)
  have hp := P.intertwines s
  have he : imaginaryCombination quaternionMatrix (R *ᵥ (TraceHessian.rotation s *ᵥ v)) *
      P.matrix =
      imaginaryCombination quaternionMatrix
        ((∑ r, R r s • TraceHessian.rotation r) *ᵥ (R *ᵥ v)) * P.matrix := by
    rw [← hw, ← hl, ← hc]
    change P.matrix * (quaternionMatrix s * imaginaryCombination quaternionMatrix v -
      imaginaryCombination quaternionMatrix v * quaternionMatrix s) =
      ((∑ r, R r s • quaternionMatrix r) *
        imaginaryCombination quaternionMatrix (R *ᵥ v) -
        imaginaryCombination quaternionMatrix (R *ᵥ v) *
          (∑ r, R r s • quaternionMatrix r)) * P.matrix
    rw [Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    · rw [← Matrix.mul_assoc, hp, Matrix.mul_assoc, hv, ← Matrix.mul_assoc]
    · rw [← Matrix.mul_assoc, hv, Matrix.mul_assoc, hp, ← Matrix.mul_assoc]
  have he' := congrArg (fun M : Mat4 => M * P.matrixᵀ) he
  simpa only [Matrix.mul_assoc, P.mul_transpose, Matrix.mul_one,
    Matrix.mulVec_mulVec] using he'

end
end PositiveEinsteinFour.QuaternionFrame

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_VarianceCorrection
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variance correction in equation (17). Equal second moments
remove the mean of the difference with the exact deficit weight. -/

namespace PositiveEinsteinFour.Variance

open MeasureTheory Filter

noncomputable section

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem variance_correction_nonneg (v b F : Ω → ℝ)
    (hv : Continuous v) (hb : Continuous b) (hF : Integrable F μ)
    (hsecond : (∫ x, v x ^ 2 ∂μ) = ∫ x, b x ^ 2 ∂μ)
    (hvariance : (∫ x, (v x - b x) ^ 2 ∂μ) - (∫ x, v x - b x ∂μ) ^ 2 ≤
      ∫ x, F x ∂μ) :
    0 ≤ ∫ x, F x - (1 - (2 - v x - b x) ^ 2 / 4) * (v x - b x) ^ 2 ∂μ := by
  let d : Ω → ℝ := fun x => v x - b x
  let w : Ω → ℝ := fun x => (2 - v x - b x) * d x
  have hd : Continuous d := hv.sub hb
  have hw : Continuous w := ((continuous_const.sub hv).sub hb).mul hd
  have intg {f : Ω → ℝ} (h : Continuous f) : Integrable f μ :=
    h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heq (x : Ω) : w x = 2 * d x - (v x ^ 2 - b x ^ 2) := by
    dsimp [w, d]
    ring
  have hv2i : Integrable (fun x => v x ^ 2) μ := intg (hv.pow 2)
  have hb2i : Integrable (fun x => b x ^ 2) μ := intg (hb.pow 2)
  have hd2i : Integrable (fun x => d x ^ 2) μ := intg (hd.pow 2)
  have hw2i : Integrable (fun x => w x ^ 2) μ := intg (hw.pow 2)
  have hmean : (∫ x, w x ∂μ) = 2 * ∫ x, d x ∂μ := by
    have hs1 := integral_sub ((intg hd).const_mul 2) (hv2i.sub hb2i)
    have hs2 := integral_sub hv2i hb2i
    simp only [Pi.sub_apply] at hs1 hs2
    rw [integral_congr_ae (Eventually.of_forall heq),
      hs1, integral_const_mul, hs2, hsecond]
    ring
  have hcs := integral_pairing_sq_le (integrable_const (1 : ℝ))
    hw2i (intg hw) (Eventually.of_forall (fun _ => zero_le_one))
    (Eventually.of_forall (fun x => sq_nonneg (w x)))
    (Eventually.of_forall (fun x => le_of_eq (one_mul (w x ^ 2)).symm))
  have hcs' : (2 * ∫ x, d x ∂μ) ^ 2 ≤ ∫ x, w x ^ 2 ∂μ := by
    simpa only [hmean, integral_const, probReal_univ, smul_eq_mul, one_mul] using hcs
  have hpoly (x : Ω) :
      (1 - (2 - v x - b x) ^ 2 / 4) * (v x - b x) ^ 2 = d x ^ 2 - w x ^ 2 / 4 := by
    dsimp [d, w]
    ring
  have hp : Integrable (fun x => (1 - (2 - v x - b x) ^ 2 / 4) * (v x - b x) ^ 2) μ := by
    apply intg
    fun_prop
  have hs := integral_sub hd2i (hw2i.div_const 4)
  rw [integral_sub hF hp, integral_congr_ae (Eventually.of_forall hpoly),
    hs, integral_div]
  change 0 ≤ (∫ x, F x ∂μ) - ((∫ x, d x ^ 2 ∂μ) - (∫ x, w x ^ 2 ∂μ) / 4)
  change (∫ x, d x ^ 2 ∂μ) - (∫ x, d x ∂μ) ^ 2 ≤ ∫ x, F x ∂μ at hvariance
  nlinarith only [hcs', hvariance]

end
end PositiveEinsteinFour.Variance

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeneralMatrixCompression
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bianchi compression for an arbitrary symmetric trace-free Weyl matrix,
with no choice of a moving diagonal frame. -/

namespace PositiveEinsteinFour.Bianchi

open scoped BigOperators
open TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem rawBianchiProjection_pairing (Z : RawGradient) (W : Tensor) (hbw : W.bianchi) :
    rawPairing (rawBianchiProjection Z) W.matrix = rawPairing Z W.matrix := by
  have hW : rawCoupling W.matrix = (-4 : ℝ) • W.matrix := by
    funext a b
    exact gradientCoupling_eq W hbw a b
  unfold rawBianchiProjection
  rw [rawPairing_smul_left, rawPairing_sub_left, rawPairing_smul_left,
    rawCoupling_selfadjoint, hW, rawPairing_smul_right]
  ring

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientMixedPairing
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bilinear matrix-slot compression on two actual Bianchi gradients. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

theorem rawMatrixCurvature_component (t : Fin 3 → ℝ) (Z : Tensor)
    (a b : Fin 3) (j : Fin 4) :
    rawMatrixCurvature t Z a b j =
      diagonalCurvatureAction t (fun a b => Z.matrix a b j) a b := by
  have hdiag (c : Fin 3) : Z.diagonal c = Z.matrix c c := by
    fin_cases c <;> rfl
  simp only [rawMatrixCurvature, diagonalCurvatureAction, hdiag]
  split_ifs
  all_goals simp [WithLp.ofLp_sum, Finset.sum_apply]
  all_goals ring

theorem rawMatrixCurvature_shape (S : Shape) (v : ℝ) (Z : Tensor) :
    rawMatrixCurvature (fun s => v * S.s s) Z = (matrixCurvatureTensor S v Z).matrix := by
  funext a b
  ext j
  rw [rawMatrixCurvature_component, matrixCurvatureTensor_matrix]

/-- The trace correction is orthogonal to the trace-free second argument. -/
theorem rawMatrixCurvature_pairing (t : Fin 3 → ℝ) (Z W : Tensor)
    (hw : W.traceFree) :
    rawPairing (rawMatrixCurvature t Z) W.matrix = diagonalGradientPairing t Z W := by
  let C : Vec := ∑ c, t c • Z.diagonal c
  have htrace : (∑ a, inner ℝ C (W.matrix a a)) = 0 := by
    have hd (a : Fin 3) : W.matrix a a = W.diagonal a := by fin_cases a <;> rfl
    simp_rw [hd]
    rw [← inner_sum, hw, inner_zero_right]
  have hcolumn : (∑ a, ∑ b, t b * inner ℝ (Z.matrix a b) (W.matrix a b)) =
      ∑ a, ∑ b, t a * inner ℝ (Z.matrix a b) (W.matrix a b) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [Z.matrix_symmetric b a, W.matrix_symmetric b a]
  have hpoint (a b : Fin 3) :
      inner ℝ (rawMatrixCurvature t Z a b) (W.matrix a b) =
        (t a * inner ℝ (Z.matrix a b) (W.matrix a b) +
          t b * inner ℝ (Z.matrix a b) (W.matrix a b)) / 2 -
            if a = b then (1 / 3 : ℝ) * inner ℝ C (W.matrix a a) else 0 := by
    by_cases hab : a = b
    · subst b
      simp only [rawMatrixCurvature, ite_true, if_true, inner_sub_left, real_inner_smul_left]
      ring
    · simp only [rawMatrixCurvature, hab, ite_false, if_false, sub_zero, real_inner_smul_left]
      ring
  rw [rawPairing_vectors]
  simp only [hpoint, Finset.sum_sub_distrib]
  simp only [← Finset.sum_div, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  have hcorrection : (∑ a, (1 / 3 : ℝ) * inner ℝ C (W.matrix a a)) = 0 := by
    rw [← Finset.mul_sum, htrace, mul_zero]
  rw [hcorrection, hcolumn]
  simp only [diagonalGradientPairing, Finset.mul_sum]
  ring

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The Ricci-commuted gradient equation for the actual metric. The two
classical slot identities remain explicit, while the differentiated trace
and curvature-divergence equations are derived. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance metricRicciNormedRing_rac3b29_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricRicciNormedSpace_rac3b29_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricRicciNormedAlgebra_rac3b29_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem rawMatrixSlice_gradientTensor (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (j : Fin 4) :
    rawMatrixSlice (gradientTensor Z).matrix j = Z j := by
  ext a b
  simp only [rawMatrixSlice, gradientTensor_matrix Z hs]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth norm regularization for the actual squared Weyl weight.
The positive regularization parameter allows the Green identities to be
used at Weyl zeros as well as on the positive-norm set. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian Filter
open scoped _root_.Topology

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.smoothWeylNormedRing
local instance smoothWeylNormedSpace_rac3b29_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.smoothWeylNormedAlgebra
theorem tendsto_regularizedBlockNorm (A : Mat) :
    Tendsto (fun ε => regularizedBlockNorm ε A) (𝓝 0) (𝓝 (normalizedBlockNorm A)) := by
  have hc : Continuous (fun ε => regularizedBlockNorm ε A) := by
    unfold regularizedBlockNorm
    fun_prop
  simpa only [regularizedBlockNorm_zero] using hc.tendsto 0

theorem tendsto_regularizedRadialDerivative (A Z : Mat) :
    Tendsto (fun ε => regularizedRadialDerivative ε A Z) (𝓝 0)
      (𝓝 (Matrix.trace (A * Z) / (6 * normalizedBlockNorm A))) := by
  by_cases ha : normalizedBlockNorm A = 0
  · have hA : A = 0 := (normalizedBlockNorm_eq_zero_iff A).mp ha
    subst A
    simp [regularizedRadialDerivative]
  · exact tendsto_const_nhds.div
      (tendsto_const_nhds.mul (tendsto_regularizedBlockNorm A))
      (mul_ne_zero (by norm_num) ha)

theorem abs_trace_mul_le_norm (A Z : Mat) (hZ : symmetric Z) :
    |Matrix.trace (A * Z)| ≤ 6 * normalizedBlockNorm A * normalizedBlockNorm Z := by
  have hzt : Zᵀ = Z := by ext i j; exact hZ j i
  have hp : matrixPairing A Z = Matrix.trace (A * Z) := by
    rw [matrixPairing_eq_trace, hzt]
  have h := real_inner_mul_inner_self_le (matrixVector A) (matrixVector Z)
  simp only [inner_matrixVector, matrixPairing_self_norm, hp] at h
  apply abs_le_of_sq_le_sq _
    (mul_nonneg (mul_nonneg (by norm_num) (normalizedBlockNorm_nonneg A))
      (normalizedBlockNorm_nonneg Z))
  nlinarith only [h]

/-- The regularized derivative has a bound independent of the smoothing
parameter. This is the domination needed at Weyl zeros. -/
theorem abs_regularizedRadialDerivative_le (ε : ℝ) (hε : 0 < ε)
    (A Z : Mat) (hZ : symmetric Z) :
    |regularizedRadialDerivative ε A Z| ≤ normalizedBlockNorm Z := by
  have hn := regularizedBlockNorm_pos ε hε A
  rw [regularizedRadialDerivative, abs_div, abs_of_pos (mul_pos (by norm_num) hn),
    div_le_iff₀ (mul_pos (by norm_num) hn)]
  calc
    _ ≤ 6 * normalizedBlockNorm A * normalizedBlockNorm Z := abs_trace_mul_le_norm A Z hZ
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (norm_le_regularizedBlockNorm ε A)
        (normalizedBlockNorm_nonneg Z)
      nlinarith only [h]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The invariant Ricci equation has the actual Bianchi compression in
every orthonormal frame, without imposing a diagonal Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open Bianchi TraceHessian

noncomputable section

/-- The arbitrary coefficient action specializes to the earlier diagonal
formula without changing the underlying matrix-slot operator. -/
theorem generalMatrixAction_diagonal (t : Fin 3 → ℝ) (Z : Tensor) :
    generalMatrixAction (Matrix.diagonal t) Z.matrix = rawMatrixCurvature t Z := by
  funext a b
  ext j
  change matrixSlotAction (Matrix.diagonal t) (rawMatrixSlice Z.matrix j) a b = _
  rw [matrixSlotAction_diagonal]
  exact (rawMatrixCurvature_component t Z a b j).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Ricci equation and its identity and varying-matrix Green
contractions in the actual arbitrary orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance metricContractionNormedRing_rac3b29_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricContractionNormedSpace_rac3b29_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricContractionNormedAlgebra_rac3b29_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem generalMatrixAction_gradientVector (A : Mat) (Z : Angular.Gradient)
    (hZ : ∀ i, symmetric (Z i)) :
    rawGradientVector (generalMatrixAction A (gradientTensor Z).matrix) =
      gradientVector (fun i => matrixSlotAction A (Z i)) := by
  ext p
  rcases p with ⟨i, a, b⟩
  change matrixSlotAction A (rawMatrixSlice (gradientTensor Z).matrix i) a b = _
  rw [rawMatrixSlice_gradientTensor Z hZ]
  rfl

theorem generalMatrixAction_gradient_pairing (A : Mat) (Z : Angular.Gradient)
    (hZ : ∀ i, symmetric (Z i)) :
    rawPairing (generalMatrixAction A (gradientTensor Z).matrix) (gradientTensor Z).matrix =
      6 * weylMatrixEnergy A Z := by
  rw [← inner_rawGradientVector, generalMatrixAction_gradientVector A Z hZ]
  change inner ℝ (gradientVector (fun i => matrixSlotAction A (Z i)))
    (tensorGradientVector (gradientTensor Z)) = _
  rw [tensorGradientVector_gradientTensor Z hZ, gradientVector_pairing]
  unfold weylMatrixEnergy
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Derivatives vanish almost everywhere on a level set. Countability of
the isolated points gives the one-dimensional statement; Fubini and
preservation of frame measure transfer it to the actual Weyl gradient. -/

namespace PositiveEinsteinFour.Geometry

open Filter Set MeasureTheory EinsteinFour TraceHessian
open scoped _root_.Topology Manifold ContDiff

noncomputable section

/-- At a non-isolated point of a level set, the ordinary derivative is zero. -/
theorem derivative_zero_at_level_accPt {f : ℝ → ℝ} {x c v : ℝ}
    (hd : HasDerivAt f v x) (hx : f x = c)
    (ha : AccPt x (𝓟 {y | f y = c})) : v = 0 := by
  have hc : HasDerivWithinAt f 0 {y | f y = c} x :=
    (hasDerivWithinAt_const x {y | f y = c} c).congr
      (fun y hy => hy) hx
  exact ha.uniqueDiffWithinAt.eq_deriv _ hd.hasDerivWithinAt hc

/-- Nonzero derivatives on any one level form a countable set. -/
theorem countable_nonzero_derivative_on_level (f df : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x) (c : ℝ) :
    {x | f x = c ∧ df x ≠ 0}.Countable := by
  let s : Set ℝ := {x | f x = c}
  apply (countable_setOfPred_isolated_right_within (s := s)).mono
  intro x hx
  refine ⟨hx.1, ?_⟩
  have ha : ¬AccPt x (𝓟 s) := fun ha =>
    hx.2 (derivative_zero_at_level_accPt (hd x) hx.1 ha)
  have hb : 𝓝[s \ {x}] x = ⊥ := by
    simpa only [accPt_principal_iff_clusterPt, ClusterPt, nhdsWithin, not_neBot] using ha
  apply le_bot_iff.mp
  rw [← hb]
  apply nhdsWithin_mono
  intro y hy
  exact ⟨hy.1, by simp only [mem_singleton_iff]; exact ne_of_gt hy.2⟩

/-- Lebesgue almost everywhere, an ordinary derivative vanishes whenever
its function lies on a specified level. -/
theorem ae_derivative_zero_on_level (f df : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x) (c : ℝ) :
    ∀ᵐ x, f x = c → df x = 0 := by
  rw [ae_iff]
  simpa only [_root_.not_imp, not_not] using
    (countable_nonzero_derivative_on_level f df hd c).measure_zero volume

/-- A measure-preserving flow transfers the one-dimensional level-set
statement to its base measure; no measure-zero assertion is a premise. -/
theorem ae_flow_derivative_zero_on_level
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    (μ : Measure Ω) [SFinite μ]
    (φ : ℝ → Ω ≃ᵐ Ω)
    (hφ : Continuous (fun p : ℝ × Ω => φ p.1 p.2))
    (hp : ∀ t, MeasurePreserving (φ t) μ μ)
    (f df : Ω → ℝ) (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀ t x, HasDerivAt (fun s => f (φ s x)) (df (φ t x)) t)
    (c : ℝ) : ∀ᵐ x ∂μ, f x = c → df x = 0 := by
  have hfc : Continuous (fun p : Ω × ℝ => f (φ p.2 p.1)) :=
    hf.comp (hφ.comp continuous_swap)
  have hdc : Continuous (fun p : Ω × ℝ => df (φ p.2 p.1)) :=
    hdf.comp (hφ.comp continuous_swap)
  have hP : MeasurableSet {p : Ω × ℝ | f (φ p.2 p.1) = c → df (φ p.2 p.1) = 0} := by
    simp only [imp_iff_not_or]
    exact (measurableSet_eq_fun hfc.measurable measurable_const).compl.union
      (measurableSet_eq_fun hdc.measurable measurable_const)
  have hline : ∀ᵐ x ∂μ, ∀ᵐ t : ℝ, f (φ t x) = c → df (φ t x) = 0 :=
    Filter.Eventually.of_forall (fun x => ae_derivative_zero_on_level
      (fun t => f (φ t x)) (fun t => df (φ t x)) (fun t => hd t x) c)
  obtain ⟨t, ht⟩ := ((Measure.ae_ae_comm hP).mp hline).exists
  rw [ae_iff] at ht ⊢
  calc
    μ {x | ¬(f x = c → df x = 0)} =
        μ ((φ t) ⁻¹' {x | ¬(f x = c → df x = 0)}) :=
      ((hp t).measure_preimage_equiv _).symm
    _ = 0 := ht

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local instance zeroLevelNormedRing_rac3b29_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance zeroLevelNormedSpace_rac3b29_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance zeroLevelNormedAlgebra_rac3b29_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
/-- The actual covariant Weyl gradient vanishes almost everywhere on the
zero set of its block. This justifies the zero-set case in the norm-weight
limit without assuming either Weyl block is everywhere nonzero. -/
theorem MetricGreenData.gradient_zero_ae_on_zero
    {g : SmoothMetric M} {μ : Measure (FrameBundle g)} [SFinite μ]
    (d : MetricGreenData g μ) :
    ∀ᵐ e ∂μ, plusWeyl g e.base e.frame = 0 →
      ∀ i, plusWeylGradient g e.base e.frame i = 0 := by
  have hc (i : Fin 4) (a b : Fin 3) :
      ∀ᵐ e ∂μ, plusWeyl g e.base e.frame a b = 0 →
        plusWeylGradient g e.base e.frame i a b = 0 :=
    ae_flow_derivative_zero_on_level μ (fun t => (d.flow i).map t)
      (d.flow i).continuous (d.flow i).preserves
      (fun e => plusWeyl g e.base e.frame a b)
      (fun e => plusWeylGradient g e.base e.frame i a b)
      ((matrixEntryMap a b).continuous.comp d.continuousWeyl)
      ((matrixEntryMap a b).continuous.comp (d.continuousGradient i))
      (fun t e => hasDerivAt_matrixEntry (d.derivativeWeyl i t e) a b) 0
  have hall : ∀ᵐ e ∂μ, ∀ i a b, plusWeyl g e.base e.frame a b = 0 →
      plusWeylGradient g e.base e.frame i a b = 0 :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun a => ae_all_iff.mpr (fun b => hc i a b)))
  filter_upwards [hall] with e he
  intro hz i
  ext a b
  apply he i a b
  exact congrArg (fun A : Mat => A a b) hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! Matrix conjugation and the derivative-index change used at a single
spectral frame. All maps act on the actual matrix arrays; no smooth choice
of eigenvectors is involved. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem conjugateMatrix_sum {ι : Type*} [Fintype ι] (R : Mat) (A : ι → Mat) :
    conjugateMatrix R (∑ i, A i) = ∑ i, conjugateMatrix R (A i) := by
  simp only [conjugateMatrix, Matrix.mul_sum, Matrix.sum_mul]

theorem conjugateMatrix_slot (R : Mat) (hR : Rᵀ * R = 1) (A B : Mat) :
    matrixSlotAction (conjugateMatrix R A) (conjugateMatrix R B) =
      conjugateMatrix R (matrixSlotAction A B) := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  simp only [matrixSlotAction_eq, conjugateMatrix_mul R hR',
    conjugateMatrix_trace R hR', conjugateMatrix_sub, conjugateMatrix_smul,
    conjugateMatrix_add, conjugateMatrix_one R hR]

theorem conjugateMatrix_traceFreeSquare (R : Mat) (hR : Rᵀ * R = 1) (A : Mat) :
    traceFreeSquare (conjugateMatrix R A) = conjugateMatrix R (traceFreeSquare A) := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  simp only [traceFreeSquare, conjugateMatrix_mul R hR',
    conjugateMatrix_trace R hR', conjugateMatrix_sub, conjugateMatrix_smul,
    conjugateMatrix_one R hR]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The quadratic and radial scalar contractions are unchanged by the
pointwise spectral frame. These are identities on finite arrays. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem matrixSlotAction_sum_smul {ι : Type*} [Fintype ι]
    (A : Mat) (c : ι → ℝ) (B : ι → Mat) :
    matrixSlotAction A (∑ j, c j • B j) = ∑ j, c j • matrixSlotAction A (B j) := by
  change (slotLinear A) (∑ j, c j • B j) = _
  rw [map_sum]
  simp only [map_smul]
  rfl

theorem turnGradient_slot (R : Mat) (hR : Rᵀ * R = 1) (P : Mat4)
    (A : Mat) (Z : Angular.Gradient) :
    (fun i => matrixSlotAction (conjugateMatrix R A) (turnGradient R P Z i)) =
      turnGradient R P (fun i => matrixSlotAction A (Z i)) := by
  funext i
  rw [turnGradient, matrixSlotAction_sum_smul]
  simp_rw [conjugateMatrix_slot R hR]
  rfl

theorem weylMatrixEnergy_turn (R : Mat) (hR : Rᵀ * R = 1)
    (P : Mat4) (hP : P * Pᵀ = 1) (A : Mat) (Z : Angular.Gradient) :
    weylMatrixEnergy (conjugateMatrix R A) (turnGradient R P Z) =
      weylMatrixEnergy A Z := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  unfold weylMatrixEnergy
  have hs := turnGradient_slot R hR P A Z
  change (∑ i, matrixPairing
    ((fun i => matrixSlotAction (conjugateMatrix R A) (turnGradient R P Z i)) i)
    (turnGradient R P Z i)) / 6 = _
  rw [hs, turnGradient_pairing R hR' P hP]

theorem weylMatrixSquareEnergy_turn (R : Mat) (hR : Rᵀ * R = 1)
    (P : Mat4) (hP : P * Pᵀ = 1) (A : Mat) (Z : Angular.Gradient) :
    weylMatrixEnergy (traceFreeSquare (conjugateMatrix R A)) (turnGradient R P Z) =
      weylMatrixEnergy (traceFreeSquare A) Z := by
  rw [conjugateMatrix_traceFreeSquare R hR, weylMatrixEnergy_turn R hR P hP]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The opposite Weyl block has the same derived gradient constraints and
zero-set calculus, using its actual parallel-frame derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem OppositeWeylData.gradientConstraints {d : MetricGreenData g μ}
    (o : OppositeWeylData d) (e : FrameBundle g) :
    (∀ i, TraceHessian.symmetric (minusWeylGradient g e.base e.frame i)) ∧
    (∀ i, TraceHessian.traceFree (minusWeylGradient g e.base e.frame i)) := by
  have hi (i : Fin 4) : TraceHessian.symmetric (minusWeylGradient g e.base e.frame i) ∧
      TraceHessian.traceFree (minusWeylGradient g e.base e.frame i) := by
    obtain ⟨e₀, he⟩ := ((d.flow i).map 0).surjective e
    change (d.flow i).map 0 e₀ = e at he
    have hs := symmetric_of_hasDerivAt (o.derivativeWeyl i 0 e₀)
      (fun t => o.symmetric ((d.flow i).map t e₀))
    have ht := traceFree_of_hasDerivAt (o.derivativeWeyl i 0 e₀)
      (fun t => o.traceFree ((d.flow i).map t e₀))
    rw [he] at hs ht
    exact ⟨hs, ht⟩
  exact ⟨fun i => (hi i).1, fun i => (hi i).2⟩

local instance oppositeZeroNormedRing_rac3b29_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance oppositeZeroNormedSpace_rac3b29_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance oppositeZeroNormedAlgebra_rac3b29_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem OppositeWeylData.gradient_zero_ae_on_zero {d : MetricGreenData g μ}
    [SFinite μ] (o : OppositeWeylData d) :
    ∀ᵐ e ∂μ, minusWeyl g e.base e.frame = 0 →
      ∀ i, minusWeylGradient g e.base e.frame i = 0 := by
  have hc (i : Fin 4) (a b : Fin 3) :
      ∀ᵐ e ∂μ, minusWeyl g e.base e.frame a b = 0 →
        minusWeylGradient g e.base e.frame i a b = 0 :=
    ae_flow_derivative_zero_on_level μ (fun t => (d.flow i).map t)
      (d.flow i).continuous (d.flow i).preserves
      (fun e => minusWeyl g e.base e.frame a b)
      (fun e => minusWeylGradient g e.base e.frame i a b)
      ((matrixEntryMap a b).continuous.comp o.continuousWeyl)
      ((matrixEntryMap a b).continuous.comp (o.continuousGradient i))
      (fun t e => hasDerivAt_matrixEntry (o.derivativeWeyl i t e) a b) 0
  have hall : ∀ᵐ e ∂μ, ∀ i a b, minusWeyl g e.base e.frame a b = 0 →
      minusWeylGradient g e.base e.frame i a b = 0 :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun a => ae_all_iff.mpr (fun b => hc i a b)))
  filter_upwards [hall] with e he
  intro hz i
  ext a b
  exact he i a b (congrArg (fun A : Mat => A a b) hz)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Covariance of the quaternionic Bianchi constraint under a genuine
oriented four-frame lift. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem turnVector_add (P : Mat4) (v w : Vec) :
    turnVector P (v + w) = turnVector P v + turnVector P w := by
  ext i
  simp only [turnVector, Matrix.mulVec, dotProduct, PiLp.add_apply,
    mul_add, Finset.sum_add_distrib]

theorem matrixAction_eq_commutator (s : Fin 3) (M : Mat) :
    matrixAction s M = TraceHessian.rotation s * M - M * TraceHessian.rotation s := by
  ext a b
  simp only [matrixAction, Matrix.sub_apply, Matrix.mul_apply,
    Finset.sum_sub_distrib]

theorem QuaternionLift.conjugate_rotation {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (hR : Rᵀ * R = 1) (s : Fin 3) :
    conjugateMatrix R (∑ r, R r s • TraceHessian.rotation r) =
      TraceHessian.rotation s := by
  have h := congrArg (fun N : Mat => Rᵀ * N) (P.rotation_intertwines s)
  simpa only [← Matrix.mul_assoc, hR, Matrix.one_mul, conjugateMatrix] using h.symm

/-- The spin-two matrix action is the conjugation action forced by the
same quaternion lift, rather than an independent representation premise. -/
theorem QuaternionLift.matrixAction_conjugate {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (hR : Rᵀ * R = 1) (s : Fin 3) (M : Mat) :
    matrixAction s (conjugateMatrix R M) =
      conjugateMatrix R (∑ r, R r s • matrixAction r M) := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  rw [matrixAction_eq_commutator, ← P.conjugate_rotation hR s,
    conjugateMatrix_mul R hR', conjugateMatrix_mul R hR', ← conjugateMatrix_sub]
  congr 1
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    matrixAction_eq_commutator, smul_sub, Finset.sum_sub_distrib]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The radial first derivative and its exact contribution to the
invariant Hessian expression. Division by a zero Weyl norm is harmless. -/

namespace PositiveEinsteinFour.Geometry

open TraceHessian HighestHessian
open scoped BigOperators

noncomputable section

theorem weylRadialSquare_eq (A : Mat) (Z : Fin 4 → Mat) :
    weylRadialSquare A Z = normalizedBlockNorm A ^ 2 * ‖blockRadialGradient A Z‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold weylRadialSquare blockRadialGradient
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [trace_eq_norm_mul_radial A (Z i)]
  ring

theorem invariantHessianForm_eq_collected (A U : Mat) (Z : Fin 4 → Mat) :
    invariantHessianForm A U Z = collectedHessianForm
      (normalizedBlockNorm A) (normalizedBlockNorm U) (weylGradientEnergy Z)
      (weylMatrixEnergy A Z) (weylMatrixEnergy (traceFreeSquare A) Z)
      (weylCompressionEnergy A Z) (‖blockRadialGradient A Z‖ ^ 2) := by
  unfold invariantHessianForm collectedHessianForm
  rw [weylRadialSquare_eq]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Covariance of the actual Bianchi projection. The two generator
transformations are derived from the same quaternion frame change and
contract against its orthogonal three-dimensional matrix. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem turnRawGradient_fieldRaw (R : Mat) (P : Mat4) (Z : Angular.Gradient) :
    turnRawGradient R P (fieldRaw Z) = fieldRaw (turnGradient R P Z) := by
  funext a b
  exact turnRawGradient_field R P Z a b

theorem turnRawGradient_add (R : Mat) (P : Mat4) (Z W : RawGradient) :
    turnRawGradient R P (Z + W) = turnRawGradient R P Z + turnRawGradient R P W := by
  funext a b
  simp only [turnRawGradient, Pi.add_apply, smul_add, Finset.sum_add_distrib,
    turnVector_add]

theorem turnRawGradient_sub (R : Mat) (P : Mat4) (Z W : RawGradient) :
    turnRawGradient R P (Z - W) = turnRawGradient R P Z - turnRawGradient R P W := by
  funext a b
  have ht : turnVector P (-∑ r, ∑ s, (R r a * R s b) • W r s) =
      -turnVector P (∑ r, ∑ s, (R r a * R s b) • W r s) := by
    simpa only [neg_one_smul] using turnVector_smul P (-1)
      (∑ r, ∑ s, (R r a * R s b) • W r s)
  simp only [turnRawGradient, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_add_neg, turnVector_add, ht]
  rfl

theorem turnRawGradient_smul (R : Mat) (P : Mat4) (c : ℝ) (Z : RawGradient) :
    turnRawGradient R P (c • Z) = c • turnRawGradient R P Z := by
  funext a b
  simp only [turnRawGradient, Pi.smul_apply, smul_comm _ c, ← Finset.smul_sum,
    turnVector_smul]

theorem turnRawGradient_sum {ι : Type*} [Fintype ι]
    (R : Mat) (P : Mat4) (Z : ι → RawGradient) :
    turnRawGradient R P (∑ i, Z i) = ∑ i, turnRawGradient R P (Z i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      funext a b
      simp [turnRawGradient, turnVector_zero]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, turnRawGradient_add, ih]

theorem rawMatrixRotation_field (s : Fin 3) (Z : Angular.Gradient) :
    rawMatrixRotation s (fieldRaw Z) = fieldRaw (fun i => matrixAction s (Z i)) := by
  funext a b
  ext i
  simp only [rawMatrixRotation, fieldRaw, PiLp.sub_apply, WithLp.ofLp_sum,
    Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, matrixAction,
    Finset.sum_sub_distrib, mul_comm]

theorem matrixAction_sum_smul {ι : Type*} [Fintype ι] (s : Fin 3)
    (c : ι → ℝ) (A : ι → Mat) :
    matrixAction s (∑ i, c i • A i) = ∑ i, c i • matrixAction s (A i) := by
  simp only [matrixAction_eq_commutator, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_sub, Finset.sum_sub_distrib]

theorem QuaternionLift.rawMatrixRotation_turn {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (hR : Rᵀ * R = 1) (s : Fin 3) (Z : RawGradient) :
    rawMatrixRotation s (turnRawGradient R P.matrix Z) =
      turnRawGradient R P.matrix (∑ r, R r s • rawMatrixRotation r Z) := by
  rw [← fieldRaw_rawField Z]
  rw [turnRawGradient_fieldRaw, rawMatrixRotation_field]
  rw [turnRawGradient_sum]
  simp_rw [turnRawGradient_smul, rawMatrixRotation_field, turnRawGradient_fieldRaw]
  funext a b
  ext i
  change matrixAction s (turnGradient R P.matrix (rawField Z) i) a b = _
  rw [turnGradient, matrixAction_sum_smul]
  simp_rw [P.matrixAction_conjugate hR, conjugateMatrix_sum, conjugateMatrix_smul]
  simp only [fieldRaw, WithLp.ofLp_sum, Finset.sum_apply, Pi.smul_apply, PiLp.smul_apply,
    turnGradient, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem quaternion_sum {ι : Type*} [Fintype ι] (s : Fin 3) (v : ι → Vec) :
    quaternion s (∑ i, v i) = ∑ i, quaternion s (v i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, quaternion_zero]
  | @insert i t hi ih => simp only [Finset.sum_insert hi, quaternion_add, ih]

theorem rawQuaternion_sum_smul {ι : Type*} [Fintype ι] (s : Fin 3)
    (c : ι → ℝ) (Z : ι → RawGradient) :
    rawQuaternion s (∑ i, c i • Z i) = ∑ i, c i • rawQuaternion s (Z i) := by
  funext a b
  simp only [rawQuaternion, Finset.sum_apply, Pi.smul_apply,
    quaternion_sum, quaternion_smul]

theorem QuaternionLift.rawQuaternion_turn {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (s : Fin 3) (Z : RawGradient) :
    rawQuaternion s (turnRawGradient R P.matrix Z) =
      turnRawGradient R P.matrix (∑ r, R r s • rawQuaternion r Z) := by
  funext a b
  simp only [rawQuaternion, turnRawGradient, P.quaternion_turnVector]
  congr 1
  simp only [quaternion_sum, quaternion_smul, Finset.sum_apply, Pi.smul_apply,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  ring

theorem rawCoupling_eq (Z : RawGradient) :
    rawCoupling Z = ∑ s, rawQuaternion s (rawMatrixRotation s Z) := by
  funext a b
  rfl

/-- The actual Casimir coupling is unchanged by the passive frame
transformation, because both of its generator indices rotate together. -/
theorem QuaternionLift.rawCoupling_turn {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (hR : Rᵀ * R = 1) (Z : RawGradient) :
    rawCoupling (turnRawGradient R P.matrix Z) =
      turnRawGradient R P.matrix (rawCoupling Z) := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  have hr (r t : Fin 3) : (∑ s, R r s * R t s) = if r = t then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun A : Mat => A r t) hR'
  rw [rawCoupling_eq]
  simp_rw [P.rawMatrixRotation_turn hR, P.rawQuaternion_turn,
    rawQuaternion_sum_smul]
  rw [← turnRawGradient_sum]
  congr 1
  calc
    _ = ∑ r, ∑ t, (∑ s, R r s * R t s) •
        rawQuaternion r (rawMatrixRotation t Z) := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]
    _ = rawCoupling Z := by
      simp only [hr, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true, if_true]
      exact (rawCoupling_eq Z).symm

theorem QuaternionLift.rawBianchiProjection_turn {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (hR : Rᵀ * R = 1) (Z : RawGradient) :
    rawBianchiProjection (turnRawGradient R P.matrix Z) =
      turnRawGradient R P.matrix (rawBianchiProjection Z) := by
  simp only [rawBianchiProjection, turnRawGradient_smul, turnRawGradient_sub,
    P.rawCoupling_turn hR]

theorem rawPairing_turn (R : Mat) (hR : R * Rᵀ = 1)
    (P : Mat4) (hP : P * Pᵀ = 1) (Z W : RawGradient) :
    rawPairing (turnRawGradient R P Z) (turnRawGradient R P W) = rawPairing Z W := by
  rw [← fieldRaw_rawField Z, ← fieldRaw_rawField W]
  simp only [turnRawGradient_fieldRaw]
  simp only [rawPairing, rawCoordinates, Fintype.sum_prod_type, fieldRaw]
  exact turnGradient_pairing R hR P hP _ _

theorem generalMatrixAction_field (A : Mat) (Z : Angular.Gradient) :
    generalMatrixAction A (fieldRaw Z) =
      fieldRaw (fun i => matrixSlotAction A (Z i)) := rfl

theorem generalMatrixAction_turn (R : Mat) (hR : Rᵀ * R = 1) (P : Mat4)
    (A : Mat) (Z : RawGradient) :
    generalMatrixAction (conjugateMatrix R A) (turnRawGradient R P Z) =
      turnRawGradient R P (generalMatrixAction A Z) := by
  rw [← fieldRaw_rawField Z]
  simp only [turnRawGradient_fieldRaw, generalMatrixAction_field]
  rw [turnGradient_slot R hR]

theorem gradientTensor_matrix_eq_fieldRaw (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) : (gradientTensor Z).matrix = fieldRaw Z := by
  funext a b
  exact gradientTensor_matrix Z hs a b

/-- The genuine squared norm of the projected matrix action is invariant
under the locally constructed frame change. -/
theorem QuaternionLift.weylCompressionEnergy_turn {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (hR : Rᵀ * R = 1) (A : Mat) (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) :
    weylCompressionEnergy (conjugateMatrix R A) (turnGradient R P.matrix Z) =
      weylCompressionEnergy A Z := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  have hs' := turnGradient_symmetric R P.matrix Z hs
  unfold weylCompressionEnergy
  rw [gradientTensor_matrix_eq_fieldRaw _ hs', gradientTensor_matrix_eq_fieldRaw Z hs,
    ← turnRawGradient_fieldRaw, generalMatrixAction_turn R hR,
    P.rawBianchiProjection_turn hR, rawPairing_turn R hR' P.matrix P.mul_transpose]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Almost-everywhere support of the norm gradient on the actual frame
bundle. A fixed positive regularization allows the level-set argument
to use ordinary smooth derivatives at every point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff

noncomputable section

local instance radialLevelNormedRing_rac3b29_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance radialLevelNormedSpace_rac3b29_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance radialLevelNormedAlgebra_rac3b29_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
private theorem regularizedRadial_zero_implies (A Z : Mat)
    (h : regularizedRadialDerivative 1 A Z = 0) :
    regularizedRadialDerivative 0 A Z = 0 := by
  have hn : 6 * regularizedBlockNorm 1 A ≠ 0 := by
    unfold regularizedBlockNorm
    positivity
  have ht : Matrix.trace (A * Z) = 0 := by
    unfold regularizedRadialDerivative at h
    exact (div_eq_zero_iff.mp h).resolve_right hn
  simp only [regularizedRadialDerivative, ht, zero_div]

private theorem radial_zero_ae_on_level
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    (μ : Measure Ω) [SFinite μ]
    (φ : Fin 4 → ℝ → Ω ≃ᵐ Ω)
    (hφ : ∀ i, Continuous (fun p : ℝ × Ω => φ i p.1 p.2))
    (hpres : ∀ i t, MeasurePreserving (φ i t) μ μ)
    (A : Ω → Mat) (Z : Fin 4 → Ω → Mat)
    (hA : Continuous A) (hZ : ∀ i, Continuous (Z i))
    (hs : ∀ x, TraceHessian.symmetric (A x))
    (hd : ∀ i t x, HasDerivAt (fun s => A (φ i s x)) (Z i (φ i t x)) t)
    (c : ℝ) :
    ∀ᵐ x ∂μ, normalizedBlockNorm (A x) = c →
      blockRadialGradient (A x) (fun i => Z i x) = 0 := by
  have hi (i : Fin 4) := ae_flow_derivative_zero_on_level μ (φ i) (hφ i) (hpres i)
    (fun x => regularizedBlockNorm 1 (A x))
    (fun x => regularizedRadialDerivative 1 (A x) (Z i x))
    ((continuous_regularizedBlockNorm 1).comp hA)
    (continuous_regularizedRadialDerivative 1 (by norm_num) A (Z i) hA (hZ i))
    (fun t x => hasDerivAt_regularizedBlockNorm (hd i t x)
      (fun s => hs (φ i s x)) (by norm_num))
    (Real.sqrt (c ^ 2 + 1))
  have hall := ae_all_iff.mpr hi
  filter_upwards [hall] with x hx
  intro hc
  ext i
  change regularizedRadialDerivative 0 (A x) (Z i x) = 0
  apply regularizedRadial_zero_implies
  apply hx i
  simp only [regularizedBlockNorm, hc, one_pow]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)} [SFinite μ]

theorem MetricGreenData.radial_zero_ae_on_level (d : MetricGreenData g μ) (c : ℝ) :
    ∀ᵐ e ∂μ, normalizedBlockNorm (plusWeyl g e.base e.frame) = c →
      blockRadialGradient (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) = 0 :=
  PositiveEinsteinFour.Geometry.radial_zero_ae_on_level μ (fun i => (d.flow i).map)
    (fun i => (d.flow i).continuous) (fun i => (d.flow i).preserves)
    _ _ d.continuousWeyl d.continuousGradient d.weyl.symmetric d.derivativeWeyl c

theorem OppositeWeylData.radial_zero_ae_on_level {d : MetricGreenData g μ}
    (o : OppositeWeylData d) (c : ℝ) :
    ∀ᵐ e ∂μ, normalizedBlockNorm (minusWeyl g e.base e.frame) = c →
      blockRadialGradient (minusWeyl g e.base e.frame)
        (minusWeylGradient g e.base e.frame) = 0 :=
  PositiveEinsteinFour.Geometry.radial_zero_ae_on_level μ (fun i => (d.flow i).map)
    (fun i => (d.flow i).continuous) (fun i => (d.flow i).preserves)
    _ _ o.continuousWeyl o.continuousGradient o.symmetric o.derivativeWeyl c

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite Bianchi triple becomes the positive triple after
reflecting only the derivative index. This gives the same invariant Kato
bound for the actual opposite Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem reflectedGradient_divergence (Z : Angular.Gradient) (r : Fin 3) (i : Fin 4) :
    gradientDivergence (reflectedGradient Z) r i = orientationSign i *
      ∑ s, ∑ j, Angular.oppositeMatrix s i j * Z j s r := by
  simp only [gradientDivergence, reflectedGradient, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro j _
  unfold Angular.oppositeMatrix oppositeQuaternion orientationSign
  split_ifs <;> ring

theorem reflectedGradient_energy (Z : Angular.Gradient) :
    weylGradientEnergy (reflectedGradient Z) = weylGradientEnergy Z := by
  unfold weylGradientEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold matrixPairing
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [reflectedGradient, Matrix.smul_apply, smul_eq_mul]
  calc
    _ = orientationSign i ^ 2 * (Z i a b * Z i a b) := by ring
    _ = _ := by rw [orientationSign_sq, one_mul]

theorem reflectedGradient_radial_norm (A : Mat) (Z : Angular.Gradient) :
    ‖blockRadialGradient A (reflectedGradient Z)‖ ^ 2 = ‖blockRadialGradient A Z‖ ^ 2 := by
  have hp (i : Fin 4) : regularizedRadialDerivative 0 A (reflectedGradient Z i) =
      orientationSign i * regularizedRadialDerivative 0 A (Z i) := by
    simp only [reflectedGradient, regularizedRadialDerivative, Matrix.mul_smul,
      Matrix.trace_smul, smul_eq_mul]
    ring
  simp only [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, regularizedRadialDerivative 0 A (reflectedGradient Z i) ^ 2) =
    ∑ i, regularizedRadialDerivative 0 A (Z i) ^ 2
  apply Finset.sum_congr rfl
  intro i _
  rw [hp, mul_pow, orientationSign_sq, one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual invariant Hessian form is bounded by its concrete spectral
parameter form. Only the negative compression-energy term is relaxed. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian HighestHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem rawPairing_self_nonneg (Z : RawGradient) : 0 ≤ rawPairing Z Z := by
  exact Finset.sum_nonneg fun p _ => mul_self_nonneg (rawCoordinates Z p)

theorem rawPairing_sub_right (Z W V : RawGradient) :
    rawPairing Z (W - V) = rawPairing Z W - rawPairing Z V := by
  rw [rawPairing_comm, rawPairing_sub_left, rawPairing_comm W, rawPairing_comm V]

/-- The explicit Bianchi curvature action is an orthogonal test of the
true projected action. Its squared norm is therefore a lower bound. -/
theorem projected_diagonal_energy_lower (S : Shape) (v : ℝ) (p k l : Vec) :
    (curvatureAction S v p k l).squaredNorm ≤
      rawPairing
        (rawBianchiProjection (generalMatrixAction
          (Matrix.diagonal (fun a => v * S.s a)) (parameters S p k l).matrix))
        (rawBianchiProjection (generalMatrixAction
          (Matrix.diagonal (fun a => v * S.s a)) (parameters S p k l).matrix)) := by
  let X := rawBianchiProjection (generalMatrixAction
    (Matrix.diagonal (fun a => v * S.s a)) (parameters S p k l).matrix)
  let Y := curvatureAction S v p k l
  have hcross : rawPairing X Y.matrix = Y.squaredNorm := by
    rw [rawBianchiProjection_pairing _ Y (parameters_bianchi S _ _ _),
      generalMatrixAction_diagonal, rawMatrixCurvature_shape, tensor_pairing_eq_raw,
      curvatureAction_compressed_energy]
    ring
  have hy : rawPairing Y.matrix Y.matrix = Y.squaredNorm := by
    rw [rawPairing_vectors]
    simp only [Tensor.squaredNorm, real_inner_self_eq_norm_sq]
  have hn := rawPairing_self_nonneg (X - Y.matrix)
  rw [rawPairing_sub_left, rawPairing_sub_right, rawPairing_sub_right,
    rawPairing_comm Y.matrix X, hcross, hy] at hn
  linarith only [hn]

theorem weylMatrixEnergy_diagonal (t : Fin 3 → ℝ) (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i)) :
    weylMatrixEnergy (Matrix.diagonal t) Z =
      (∑ a, t a * ∑ b, ‖(gradientTensor Z).matrix a b‖ ^ 2) / 6 := by
  have h := generalMatrixAction_gradient_pairing (Matrix.diagonal t) Z hs
  rw [generalMatrixAction_diagonal, rawMatrixCurvature_pairing _ _ _
    (gradientTensor_traceFree Z ht)] at h
  simp only [diagonalGradientPairing, real_inner_self_eq_norm_sq] at h
  linarith only [h]

theorem weighted_row_norms (w : Fin 3 → ℝ) (hw : ∑ a, w a = 0) (T : Tensor) :
    (∑ a, w a * ∑ b, ‖T.matrix a b‖ ^ 2) =
      (∑ a, w a * ‖T.diagonal a‖ ^ 2) - ∑ a, w a * ‖T.off a‖ ^ 2 := by
  simp only [Fin.sum_univ_three] at hw
  simp [Tensor.matrix, Fin.sum_univ_three]
  linear_combination (‖T.off 0‖ ^ 2 + ‖T.off 1‖ ^ 2 + ‖T.off 2‖ ^ 2) * hw

theorem weylMatrixEnergy_shape (S : Shape) (v : ℝ) (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i)) :
    weylMatrixEnergy (Matrix.diagonal (fun a => v * S.s a)) Z =
      curvatureContraction S v (gradientTensor Z) := by
  rw [weylMatrixEnergy_diagonal _ Z hs ht]
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [weighted_row_norms S.s S.trace]
  unfold curvatureContraction
  ring

theorem shape_traceFreeSquare (S : Shape) (v : ℝ) :
    traceFreeSquare (Matrix.diagonal (fun a => v * S.s a)) =
      Matrix.diagonal (fun a => v ^ 2 * S.squareWeight a) := by
  have hsum : (∑ a, (v * S.s a) ^ 2) = 6 * v ^ 2 := by
    simp only [mul_pow, ← Finset.mul_sum, S.square]
    ring
  unfold traceFreeSquare
  rw [Matrix.diagonal_mul_diagonal]
  have htrace : Matrix.trace (Matrix.diagonal
      (fun a => (v * S.s a) * (v * S.s a))) = 6 * v ^ 2 := by
    simpa only [Matrix.trace_diagonal, ← pow_two] using hsum
  rw [htrace]
  ext a b
  by_cases hab : a = b
  · subst b
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      Matrix.diagonal_apply_eq, smul_eq_mul, mul_one, Shape.squareWeight]
    ring
  · simp [Matrix.sub_apply, Matrix.smul_apply, hab]

theorem weylMatrixEnergy_squareShape (S : Shape) (v : ℝ) (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i)) :
    weylMatrixEnergy (traceFreeSquare (Matrix.diagonal (fun a => v * S.s a))) Z =
      squareCurvatureContraction S v (gradientTensor Z) := by
  have hw : ∑ a, S.squareWeight a = 0 := by
    simp only [Shape.squareWeight, Finset.sum_sub_distrib, S.square,
      Finset.sum_const, Finset.card_fin]
    norm_num
  rw [shape_traceFreeSquare, weylMatrixEnergy_diagonal _ Z hs ht]
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [weighted_row_norms S.squareWeight hw]
  unfold squareCurvatureContraction
  ring

/-- All scalar contractions needed by the source Hessian form can be
evaluated in the single pointwise spectral frame. No smooth eigenframe
or second-block diagonalization is involved. -/
theorem invariantHessianForm_spectral_upper_of_frame (A U : Mat) (Z : Angular.Gradient)
    (R : Mat) (hR : Rᵀ * R = 1)
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (S : Shape)
    (hS : conjugateMatrix R A = Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i))
    (hv : 0 < normalizedBlockNorm A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0) :
    ∃ (p k l : Vec),
      (parameters S p k l).squaredNorm / 6 = weylGradientEnergy Z ∧
      ‖p‖ ^ 2 = ‖blockRadialGradient A Z‖ ^ 2 ∧
      weylMatrixEnergy A Z =
        curvatureContraction S (normalizedBlockNorm A) (parameters S p k l) ∧
      invariantHessianForm A U Z ≤
        hessianTensorForm S (normalizedBlockNorm A) (normalizedBlockNorm U) p k l := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  let W := turnGradient R P.matrix Z
  let T := gradientTensor W
  let p := radialCoordinate S T
  let k := secondCoordinate S T
  let l := thirdCoordinate S T
  have hsW := turnGradient_symmetric R P.matrix Z hs
  have htW := turnGradient_traceFree R hR' P.matrix Z ht
  have hbW := turnGradient_bianchi R hR' P Z hb
  have hT : parameters S p k l = T :=
    parameters_reconstruction S T (gradientTensor_traceFree W htW)
      (gradientTensor_bianchi W hsW hbW)
  have he : T.squaredNorm / 6 = weylGradientEnergy Z := by
    rw [gradientTensor_energy W hsW, weylGradientEnergy_turn R hR' P.matrix P.mul_transpose]
  have hrad : ‖p‖ ^ 2 = ‖blockRadialGradient A Z‖ ^ 2 := by
    have hnorm : normalizedBlockNorm (Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i)) =
        normalizedBlockNorm A := by rw [← hS]; exact conjugateMatrix_norm R hR' A
    have hp : blockRadialGradient (conjugateMatrix R A) W = p := by
      rw [show conjugateMatrix R A = _ from hS,
        blockRadialGradient_diagonal S (normalizedBlockNorm A) W, hnorm,
        div_self (ne_of_gt hv), one_smul]
    have hr := blockRadialGradient_turn R hR' P.matrix A Z
    rw [hp] at hr
    rw [hr, turnVector_norm P.matrix P.mul_transpose]
  have hB : weylMatrixEnergy A Z = curvatureContraction S (normalizedBlockNorm A) T := by
    rw [← weylMatrixEnergy_turn R hR P.matrix P.mul_transpose, show conjugateMatrix R A = _ from hS]
    exact weylMatrixEnergy_shape S _ W hsW htW
  have hC : weylMatrixEnergy (traceFreeSquare A) Z =
      squareCurvatureContraction S (normalizedBlockNorm A) T := by
    rw [← weylMatrixSquareEnergy_turn R hR P.matrix P.mul_transpose,
      show conjugateMatrix R A = _ from hS]
    exact weylMatrixEnergy_squareShape S _ W hsW htW
  have hE : (curvatureAction S (normalizedBlockNorm A) p k l).squaredNorm / 6 ≤
      weylCompressionEnergy A Z := by
    rw [← P.weylCompressionEnergy_turn hR A Z hs,
      show conjugateMatrix R A = _ from hS]
    unfold weylCompressionEnergy
    change (curvatureAction S (normalizedBlockNorm A) p k l).squaredNorm / 6 ≤
      rawPairing
        (rawBianchiProjection (generalMatrixAction
          (Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i)) T.matrix))
        (rawBianchiProjection (generalMatrixAction
          (Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i)) T.matrix)) / 6
    rw [← hT]
    exact div_le_div_of_nonneg_right (projected_diagonal_energy_lower S _ p k l)
      (by norm_num)
  refine ⟨p, k, l, ?_, hrad, ?_, ?_⟩
  · rw [hT]
    exact he
  · rw [hT]
    exact hB
  · rw [invariantHessianForm_eq_collected]
    unfold collectedHessianForm hessianTensorForm
    rw [hB, hC, ← he, ← hT, ← hrad]
    linarith only [hE]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Integrability at a zero Weyl norm is obtained from uniformly bounded
regularized energies and Fatou's lemma. No integrability of the singular
quotient is assumed in the limiting argument. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter TraceHessian
open scoped BigOperators _root_.Topology

noncomputable section

theorem integrable_of_ae_limit_norm_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : ℕ → Ω → ℝ) (f : Ω → ℝ) (C : ℝ)
    (hF : ∀ n, Integrable (F n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hbound : ∀ n, (∫ x, ‖F n x‖ ∂μ) ≤ C) : Integrable f μ := by
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (hF n).aestronglyMeasurable) hlim, ?_⟩
  have hf : (∫⁻ x, ‖f x‖ₑ ∂μ) ≤
      liminf (fun n => ∫⁻ x, ‖F n x‖ₑ ∂μ) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => ‖F n x‖ₑ) atTop ∂μ :=
        lintegral_congr_ae (hlim.mono (fun x hx => hx.enorm.liminf_eq.symm))
      _ ≤ _ := lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.enorm)
  have hb : liminf (fun n => ∫⁻ x, ‖F n x‖ₑ ∂μ) atTop ≤ ENNReal.ofReal C := by
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
    apply iSup_le
    intro n
    refine (iInf₂_le n le_rfl).trans ?_
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hF n)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  exact lt_of_le_of_lt (hf.trans hb) ENNReal.ofReal_lt_top

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationFrameClass_proj
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The raw orthogonal-frame invariance used from Brin--Karcher, §1:
the uniform frame measure is invariant under a fixed reflection, and
parallel transport intertwines reflection with reversal of the first
flow direction. This gives integral and tensor identities for reflected frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem regularizedRadialDerivative_smul (ε : ℝ) (A Z : Mat) (c : ℝ) :
    regularizedRadialDerivative ε A (c • Z) = c * regularizedRadialDerivative ε A Z := by
  simp only [regularizedRadialDerivative, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

theorem reflectedGradient_radial_sum (ε : ℝ) (A : Mat) (Z : Angular.Gradient) :
    (∑ i, regularizedRadialDerivative ε A (reflectedGradient Z i) ^ 2) =
      ∑ i, regularizedRadialDerivative ε A (Z i) ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  rw [reflectedGradient, regularizedRadialDerivative_smul, mul_pow, orientationSign_sq, one_mul]

theorem scalarNormExpression_reflected (ε : ℝ) (A : Mat) (Z : Angular.Gradient) :
    scalarNormExpression ε A (reflectedGradient Z) = scalarNormExpression ε A Z := by
  unfold scalarNormExpression
  rw [reflectedGradient_energy, reflectedGradient_radial_sum]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrability of the scalar weak equation and of its radial terms.
The estimates use the actual metric Kato bound, including the zero set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

namespace MetricGreenData

theorem radial_integrable (d : MetricGreenData g μ) (i : Fin 4) :
    Integrable (fun e => regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i)) μ := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  let H : C(FrameBundle g, ℝ) := ⟨fun e => normalizedBlockNorm
    (plusWeylGradient g e.base e.frame i),
    continuous_normalizedBlockNorm.comp (d.continuousGradient i)⟩
  have hF (n) : Integrable (fun e => d.regularizedRadialField (ε n) (hε n) i e) μ :=
    (d.regularizedRadialField (ε n) (hε n) i).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply integrable_of_ae_limit_norm_bound μ
    (fun n e => d.regularizedRadialField (ε n) (hε n) i e) _ (∫ e, H e ∂μ) hF
  · filter_upwards [] with e
    simpa only [ε, regularizedRadialField, ContinuousMap.coe_mk, Function.comp_def,
      regularizedRadialDerivative, regularizedBlockNorm_zero] using
      (tendsto_regularizedRadialDerivative (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i)).comp tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    apply integral_mono_ae (hF n).norm
      (H.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    filter_upwards [] with e
    rw [Real.norm_eq_abs]
    exact abs_regularizedRadialDerivative_le (ε n) (hε n) _ _ ((d.gradientConstraints e).1 i)

end MetricGreenData

omit [IsFiniteMeasure μ] in
theorem integrable_continuous_weight {f : FrameBundle g → ℝ} (hf : Integrable f μ)
    (k : C(FrameBundle g, ℝ)) : Integrable (fun e => k e * f e) μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn k.continuous.continuousOn
  exact hf.bdd_mul k.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => hC e (Set.mem_univ e)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Symmetrize an oriented frame measure only for the reflection-invariant
Green integral. Scalar variance and Weyl gaps still use the original
oriented measure. Reflection invariance of that original measure is not
assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem reflection_preserves_symmetricFrameMeasure :
    MeasurePreserving (frameReflection : FrameBundle g → FrameBundle g)
      (symmetricFrameMeasure g μ) (symmetricFrameMeasure g μ) := by
  have hF : Measurable (frameReflection : FrameBundle g → FrameBundle g) :=
    (frameReflectionEquiv g).measurable
  have hinv : (μ.map frameReflection).map frameReflection = μ := by
    rw [Measure.map_map hF hF]
    have hf : (frameReflection : FrameBundle g → FrameBundle g) ∘ frameReflection = id :=
      funext (frameReflection_involutive g)
    rw [hf, Measure.map_id]
  refine ⟨hF, ?_⟩
  rw [symmetricFrameMeasure, Measure.map_add _ _ hF, hinv, add_comm]

theorem OppositeWeylData.onSymmetricMeasure {d : MetricGreenData g μ}
    (o : OppositeWeylData d) (hparallel : ParallelReflection d) :
    OppositeWeylData (d.onSymmetricMeasure hparallel) where
  symmetric := o.symmetric
  traceFree := o.traceFree
  continuousWeyl := o.continuousWeyl
  continuousGradient := o.continuousGradient
  derivativeWeyl := o.derivativeWeyl
  gradientBianchi := o.gradientBianchi

theorem MetricGreenData.symmetricReflection (d : MetricGreenData g μ)
    (hparallel : ParallelReflection d) : FrameReflectionData (d.onSymmetricMeasure hparallel) where
  preserves := reflection_preserves_symmetricFrameMeasure
  parallel := hparallel

end
end PositiveEinsteinFour.Geometry
end


section

/-! Test both actual scalar Weyl equations against the total derivative
energy. This is the norm-equation half of the cancellation in (16). -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

include r

theorem opposite_radial_integrable (i : Fin 4) :
    Integrable (fun e => regularizedRadialDerivative 0 (minusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame i)) μ := by
  have h := (r.preserves.integrable_comp_of_integrable (d.radial_integrable i)).const_mul
    (orientationSign i)
  apply h.congr
  filter_upwards [] with e
  change orientationSign i * regularizedRadialDerivative 0
    (plusWeyl g e.base e.frame.reflect) (plusWeylGradient g e.base e.frame.reflect i) = _
  rw [plusWeyl_reflect, plusWeylGradient_reflect, regularizedRadialDerivative_smul,
    ← mul_assoc, ← pow_two, orientationSign_sq, one_mul]

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite and summed deficit tests, obtained from the same
proved plus-block energy identity by reflection of the actual frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem minusWeylGradient_reflect (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (i : Fin 4) :
    minusWeylGradient g c e.reflect i = orientationSign i • plusWeylGradient g c e i := by
  have h := plusWeylGradient_reflect g c e.reflect i
  rw [e.reflect_reflect] at h
  have h' := congrArg (fun A : Mat => orientationSign i • A) h
  rw [smul_smul, ← pow_two, orientationSign_sq, one_smul] at h'
  exact h'.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! A pointwise spectral witness retains exactly the data used by the
coupled estimate. The witness is constructed from the actual matrices
and Bianchi gradient; it never requires a measurable spectral frame. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry
open Energy QuarticEnergy Quadratic Potential

noncomputable section

/-- All fields, including the Hessian upper bound, come from the proved
finite-dimensional identities. -/
theorem pointwiseSpectrum_nonempty (A U : Mat) (Z : Angular.Gradient) (p : Vec)
    (hA : symmetric A) (htA : traceFree A) (hv : 0 < normalizedBlockNorm A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0)
    (hp : ‖p‖ ^ 2 = ‖blockRadialGradient A Z‖ ^ 2) :
    Nonempty (PointwiseSpectrum A U Z p) := by
  obtain ⟨R, hR, ⟨P⟩, S, hdiag⟩ := exists_lifted_spectral_shape A hA htA hv
  obtain ⟨r, hr, hr2, hσ, hlo, hmin⟩ := shape_exists_minimum_parameter S
  obtain ⟨p', k, l, he, hrad, hB, hH⟩ :=
    invariantHessianForm_spectral_upper_of_frame A U Z R hR P S hdiag hv hs ht hb
  exact ⟨{
    frame := R
    orthogonal := hR
    shape := S
    diagonal := hdiag
    minimum := r
    minimum_lower := hr
    minimum_upper := hr2
    cubic := hσ
    spectrum_lower := hlo
    spectrum_minimum := hmin
    radial := p'
    second := k
    third := l
    energy := he
    radial_norm := hrad.trans hp.symm
    original_radial_norm := hp.symm
    matrix_energy := hB
    hessian := hH }⟩

namespace PointwiseSpectrum

variable {A U : Mat} {Z : Angular.Gradient} {p : Vec}

theorem energy_lower (D : PointwiseSpectrum A U Z p) :
    (5 / 3 : ℝ) * ‖p‖ ^ 2 ≤ weylGradientEnergy Z := by
  have h := D.energy
  rw [parameters_energy, D.radial_norm] at h
  nlinarith only [h, sq_nonneg ‖D.second‖, sq_nonneg ‖D.third‖]

theorem shape_circle (D : PointwiseSpectrum A U Z p) :
    D.shape.rho ^ 2 = 1 - D.shape.sigma ^ 2 := by
  linarith only [D.shape.sigma_rho_circle]

theorem minimum_le_shift (D : PointwiseSpectrum A U Z p) (x : ℝ)
    (hAx : (A + x • (1 : Mat)).PosSemidef) :
    normalizedBlockNorm A * D.minimum ≤ x :=
  shape_minimum_parameter_bound A D.frame D.orthogonal D.shape _ x D.minimum
    D.diagonal hAx D.spectrum_minimum

end PointwiseSpectrum

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Zero-axis extensions require the gradient to vanish at the zero
block. This is the almost-everywhere property proved separately from
the actual frame flow; it is not inferred from the block value alone. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry
open Energy QuarticEnergy Quadratic Potential

noncomputable section

theorem zero_gradient_energy : weylGradientEnergy (0 : Angular.Gradient) = 0 := by
  simp [weylGradientEnergy, matrixPairing]

theorem zero_gradient_matrix_energy (A : Mat) :
    weylMatrixEnergy A (0 : Angular.Gradient) = 0 := by
  simp [weylMatrixEnergy, matrixPairing]

theorem zero_gradient_radial (A : Mat) :
    blockRadialGradient A (0 : Angular.Gradient) = 0 := by
  ext i
  simp [blockRadialGradient, regularizedRadialDerivative]

theorem zero_gradient_hessian_nonpos (A U : Mat) :
    invariantHessianForm A U (0 : Angular.Gradient) ≤ 0 := by
  have he : 0 ≤ weylCompressionEnergy A (0 : Angular.Gradient) := by
    unfold weylCompressionEnergy
    exact div_nonneg (rawPairing_self_nonneg _) (by norm_num)
  have hr : weylRadialSquare A (0 : Angular.Gradient) = 0 := by
    simp [weylRadialSquare]
  unfold invariantHessianForm
  rw [zero_gradient_energy, zero_gradient_matrix_energy, zero_gradient_matrix_energy, hr]
  nlinarith only [he]

theorem pointwiseSpectrum_zero (U : Mat) :
    Nonempty (PointwiseSpectrum 0 U (0 : Angular.Gradient) (0 : Vec)) := by
  have hv : normalizedBlockNorm (0 : Mat) = 0 :=
    (normalizedBlockNorm_eq_zero_iff _).mpr rfl
  refine ⟨{
    frame := 1
    orthogonal := by simp
    shape := costShape
    diagonal := by simp [conjugateMatrix, hv]
    minimum := 1
    minimum_lower := le_rfl
    minimum_upper := by norm_num
    cubic := by norm_num [Shape.sigma, costShape, Fin.sum_univ_three]
    spectrum_lower := by intro i; fin_cases i <;> norm_num [costShape]
    spectrum_minimum := ⟨0, by norm_num [costShape]⟩
    radial := 0
    second := 0
    third := 0
    energy := by rw [parameters_energy, zero_gradient_energy]; simp
    radial_norm := rfl
    original_radial_norm := by rw [zero_gradient_radial]
    matrix_energy := by
      rw [zero_gradient_matrix_energy, curvatureContraction_parameters]
      simp
    hessian := ?_ }⟩
  have hh := zero_gradient_hessian_nonpos (0 : Mat) U
  simpa only [hessianTensor_matrix, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    inner_zero_left, inner_zero_right, mul_zero, add_zero, sub_zero] using hh

theorem pointwiseSpectrum_nonempty_closed (A U : Mat) (Z : Angular.Gradient) (p : Vec)
    (hA : symmetric A) (htA : traceFree A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0)
    (hp : ‖p‖ ^ 2 = ‖blockRadialGradient A Z‖ ^ 2)
    (hzero : normalizedBlockNorm A = 0 → Z = 0) :
    Nonempty (PointwiseSpectrum A U Z p) := by
  by_cases hv : normalizedBlockNorm A = 0
  · have hAz : A = 0 := (normalizedBlockNorm_eq_zero_iff A).mp hv
    have hZz := hzero hv
    have hpz : p = 0 := by
      rw [hZz, zero_gradient_radial, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hp
      exact norm_eq_zero.mp (by nlinarith only [hp, norm_nonneg p])
    subst A
    subst Z
    subst p
    exact pointwiseSpectrum_zero U
  · exact pointwiseSpectrum_nonempty A U Z p hA htA
      (lt_of_le_of_ne (normalizedBlockNorm_nonneg A) (Ne.symm hv)) hs ht hb hp

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The actual two-block finite-array integrand is bounded using the
constructed spectral data. All spectral choices disappear from the final
estimate, including zero axes where the actual gradient vanishes. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian HighestHessian PositiveEinsteinFour.Geometry
open Energy QuarticEnergy Quadratic Potential Boundary

noncomputable section

/-- The same bound includes both zero axes under precisely the
gradient-vanishing hypotheses supplied almost everywhere by the flow. -/
theorem pointwise_coupling_bound_closed
    (A U : Mat) (Z V : Angular.Gradient) (a ab p q : Vec)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (hZs : ∀ i, symmetric (Z i)) (hZt : ∀ i, traceFree (Z i))
    (hZb : ∀ r i, gradientDivergence Z r i = 0)
    (hVs : ∀ i, symmetric (V i)) (hVt : ∀ i, traceFree (V i))
    (hVb : ∀ r i, gradientDivergence V r i = 0)
    (hzero : normalizedBlockNorm A = 0 → Z = 0)
    (hzerob : normalizedBlockNorm U = 0 → V = 0)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (hp : ‖p‖ ^ 2 = ‖blockRadialGradient A Z‖ ^ 2)
    (hq : ‖q‖ ^ 2 = ‖blockRadialGradient U V‖ ^ 2)
    (ha : ‖a‖ ^ 2 = (9 / 16 : ℝ) * scalarWeight (normalizedBlockNorm A) (normalizedBlockNorm U) ^ 2 *
      ‖p - q‖ ^ 2)
    (hab : ‖ab‖ ^ 2 = (9 / 16 : ℝ) * scalarWeight (normalizedBlockNorm U) (normalizedBlockNorm A) ^ 2 *
      ‖p - q‖ ^ 2) :
    arrayCoupledIntegrand A U Z V a ab p q ≤
      -couplingCoefficient (normalizedBlockNorm A) (normalizedBlockNorm U) *
        (‖p‖ ^ 2 + ‖q‖ ^ 2) *
          (‖p‖ ^ 2 / normalizedBlockNorm A + ‖q‖ ^ 2 / normalizedBlockNorm U) +
      2 * theta (normalizedBlockNorm A) (normalizedBlockNorm U) *
        (normWeight (normalizedBlockNorm A) * ‖p‖ ^ 2 +
          normWeight (normalizedBlockNorm U) * ‖q‖ ^ 2) -
      theta (normalizedBlockNorm A) (normalizedBlockNorm U) ^ 2 /
        couplingCoefficient (normalizedBlockNorm A) (normalizedBlockNorm U) := by
  obtain ⟨D⟩ := pointwiseSpectrum_nonempty_closed A U Z p hA htA hZs hZt hZb hp hzero
  obtain ⟨F⟩ := pointwiseSpectrum_nonempty_closed U A V q hU htU hVs hVt hVb hq hzerob
  have hmin : normalizedBlockNorm A * D.minimum + normalizedBlockNorm U * F.minimum ≤ 2 := by
    have hd := D.minimum_le_shift x hAx
    have hf := F.minimum_le_shift y hUy
    linarith only [hd, hf, hxy]
  apply (arrayCoupledIntegrand_le_reduced A U Z V a ab p q hA hU htA htU
    hZs hZt hZb hVs hVt hVb hzero hzerob D F hmin ha hab).trans
  exact reduced_integrand_bound p q (normalizedBlockNorm_nonneg A) (normalizedBlockNorm_nonneg U)
    D.minimum_lower D.minimum_upper F.minimum_lower F.minimum_upper hmin
    D.cubic D.shape_circle F.cubic F.shape_circle D.energy_lower F.energy_lower
    (by intro h; rw [hzero h, zero_gradient_energy])
    (by intro h; rw [hzerob h, zero_gradient_energy])

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Integrability of the products in the two polynomial norm tests.
The norm derivatives are obtained by their actual regularized limits. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

theorem abs_radialDerivative_zero_le (A Z : Mat) (hZ : symmetric Z) :
    |regularizedRadialDerivative 0 A Z| ≤ normalizedBlockNorm Z := by
  have ht : Tendsto (fun n : ℕ => regularizedRadialDerivative
      (1 / ((n : ℝ) + 1)) A Z) atTop (𝓝 (regularizedRadialDerivative 0 A Z)) := by
    simpa only [Function.comp_def, regularizedRadialDerivative,
      regularizedBlockNorm_zero] using
      (tendsto_regularizedRadialDerivative A Z).comp
        tendsto_one_div_add_atTop_nhds_zero_nat
  exact le_of_tendsto ht.abs (Eventually.of_forall (fun n =>
    abs_regularizedRadialDerivative_le _ (by positivity) A Z hZ))

section Integral

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

local instance jointIntegrabilityRing_rac3b29_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance jointIntegrabilitySpace_rac3b29_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance jointIntegrabilityAlgebra_rac3b29_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem integrable_radialDerivative_product
    (A B Z V : Ω → Mat) (hZ : Continuous Z) (hV : Continuous V)
    (hsZ : ∀ x, symmetric (Z x)) (hsV : ∀ x, symmetric (V x))
    (hp : AEStronglyMeasurable (fun x => regularizedRadialDerivative 0 (A x) (Z x)) μ)
    (hq : AEStronglyMeasurable (fun x => regularizedRadialDerivative 0 (B x) (V x)) μ) :
    Integrable (fun x => regularizedRadialDerivative 0 (A x) (Z x) *
      regularizedRadialDerivative 0 (B x) (V x)) μ := by
  have hc := (continuous_normalizedBlockNorm.comp hZ).mul
    (continuous_normalizedBlockNorm.comp hV)
  apply (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mono'
    (hp.mul hq)
  filter_upwards [] with x
  change ‖regularizedRadialDerivative 0 (A x) (Z x) *
    regularizedRadialDerivative 0 (B x) (V x)‖ ≤ normalizedBlockNorm (Z x) * normalizedBlockNorm (V x)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (abs_radialDerivative_zero_le _ _ (hsZ x))
    (abs_radialDerivative_zero_le _ _ (hsV x)) (abs_nonneg _)
    (normalizedBlockNorm_nonneg _)

end Integral

end
end PositiveEinsteinFour.Geometry
end


section

/-! Express the reflected continuous fields as the actual opposite-block
contractions, so the trace-energy inequality can be used in scalar form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem matrixSlotAction_smul_right (A Z : Mat) (c : ℝ) :
    matrixSlotAction A (c • Z) = c • matrixSlotAction A Z := by
  simpa using QuaternionFrame.matrixSlotAction_sum_smul (ι := Unit) A (fun _ => c) (fun _ => Z)

theorem matrixPairing_same_smul (A B : Mat) (c : ℝ) :
    matrixPairing (c • A) (c • B) = c ^ 2 * matrixPairing A B := by
  simp only [matrixPairing, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weylMatrixEnergy_reflected (A : Mat) (Z : Angular.Gradient) :
    weylMatrixEnergy A (reflectedGradient Z) = weylMatrixEnergy A Z := by
  unfold weylMatrixEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [reflectedGradient, matrixSlotAction_smul_right, matrixPairing_same_smul,
    orientationSign_sq, one_mul]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

theorem jointMatrixEnergy_apply (d : MetricGreenData g μ) (e : FrameBundle g) :
    d.jointMatrixEnergy e =
      weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) +
      weylMatrixEnergy (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame) := by
  have hz : plusWeylGradient g e.base e.frame.reflect =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  change _ + weylMatrixEnergy (plusWeyl g e.base e.frame.reflect)
    (plusWeylGradient g e.base e.frame.reflect) = _
  rw [plusWeyl_reflect, hz, weylMatrixEnergy_reflected]
  rfl

theorem jointTraceEnergy_apply (d : MetricGreenData g μ) (e : FrameBundle g) :
    d.jointTraceEnergy e = traceEnergy (plusWeyl g e.base e.frame) +
      traceEnergy (minusWeyl g e.base e.frame) := by
  change _ + traceEnergy (plusWeyl g e.base e.frame.reflect) = _
  rw [plusWeyl_reflect]

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identify the actual metric integral with the finite-array integrand.
Only fixed frame reflection is used for the second Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi QuaternionFrame MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem reflectedVector_norm (p : Vec) : ‖reflectedVector p‖ = ‖p‖ := by
  have hs : ‖reflectedVector p‖ ^ 2 = ‖p‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, reflectedVector, mul_pow,
      orientationSign_sq, one_mul]
  nlinarith [norm_nonneg (reflectedVector p), norm_nonneg p]

theorem weylWeightGradient_eq (A U : Mat) (Z V : Angular.Gradient) :
    weylWeightGradient A U Z V =
      (-(3 / 4 : ℝ) * (1 - (3 / 8 : ℝ) * (normalizedBlockNorm A - normalizedBlockNorm U))) •
        (blockRadialGradient A Z - blockRadialGradient U V) := by
  ext i
  simp only [weylWeightGradient, regularizedWeylWeightDerivative,
    regularizedBlockNorm_zero, blockRadialGradient, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul]

theorem weylWeightGradient_reflected (A U : Mat) (Z V : Angular.Gradient) :
    weylWeightGradient A U (reflectedGradient Z) (reflectedGradient V) =
      reflectedVector (weylWeightGradient A U Z V) := by
  ext i
  change regularizedWeylWeightDerivative 0 A U
    (orientationSign i • Z i) (orientationSign i • V i) = _
  unfold regularizedWeylWeightDerivative
  rw [regularizedRadialDerivative_smul, regularizedRadialDerivative_smul]
  change _ = orientationSign i * regularizedWeylWeightDerivative 0 A U (Z i) (V i)
  unfold regularizedWeylWeightDerivative
  ring

theorem kappaNormIntegrand_pair (A U : Mat) (Z V : Angular.Gradient) :
    kappaNormIntegrand A U Z V + kappaNormIntegrand U A V Z =
      Potential.kappa (normalizedBlockNorm A) (normalizedBlockNorm U) * scalarNormExpression 0 A Z +
      Potential.kappa (normalizedBlockNorm U) (normalizedBlockNorm A) * scalarNormExpression 0 U V +
      Quadratic.kappaV (normalizedBlockNorm A) (normalizedBlockNorm U) * ‖blockRadialGradient A Z‖ ^ 2 +
      (Quadratic.kappaB (normalizedBlockNorm A) (normalizedBlockNorm U) +
        Quadratic.kappaB (normalizedBlockNorm U) (normalizedBlockNorm A)) *
          inner ℝ (blockRadialGradient A Z) (blockRadialGradient U V) +
      Quadratic.kappaV (normalizedBlockNorm U) (normalizedBlockNorm A) * ‖blockRadialGradient U V‖ ^ 2 := by
  simp only [kappaNormIntegrand, regularizedKappa, regularizedKappaDerivative,
    regularizedBlockNorm_zero, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, blockRadialGradient]
  simp only [Finset.sum_add_distrib, add_mul, Fin.sum_univ_four]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem regularizedHessianIntegrand_eq_arrayHessianTerm (e : FrameBundle g) :
    regularizedHessianIntegrand g 0 e =
      arrayHessianTerm (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame)
        (weylWeightGradient (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame) (minusWeylGradient g e.base e.frame)) := by
  unfold regularizedHessianIntegrand arrayHessianTerm weylWeightGradient
    regularizedWeylWeight Quadratic.weight weightedCubicField
  simp only [regularizedBlockNorm_zero]
  congr 2 <;> ring

theorem reflectedHessianIntegrand_eq_arrayHessianTerm (e : FrameBundle g) :
    regularizedHessianIntegrand g 0 (frameReflection e) =
      arrayHessianTerm (minusWeyl g e.base e.frame) (plusWeyl g e.base e.frame)
        (reflectedGradient (minusWeylGradient g e.base e.frame))
        (reflectedVector (weylWeightGradient (minusWeyl g e.base e.frame) (plusWeyl g e.base e.frame)
          (minusWeylGradient g e.base e.frame) (plusWeylGradient g e.base e.frame))) := by
  rw [regularizedHessianIntegrand_eq_arrayHessianTerm]
  have hp : plusWeylGradient g e.base e.frame.reflect =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  have hm : minusWeylGradient g e.base e.frame.reflect =
      reflectedGradient (plusWeylGradient g e.base e.frame) := by
    funext i
    exact minusWeylGradient_reflect g e.base e.frame i
  dsimp only [frameReflection]
  rw [plusWeyl_reflect, minusWeyl_reflect, hp, hm, weylWeightGradient_reflected]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full finite-array integrand is the actual metric integral from
both Green identities, trace subtraction, variance, and polynomial tests. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi QuaternionFrame MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem scalarCouplingTerm_eq_trace_and_tests (A U : Mat) (Z V : Angular.Gradient) :
    scalarCouplingTerm (normalizedBlockNorm A) (normalizedBlockNorm U)
      (weylGradientEnergy Z) (weylGradientEnergy V)
      (weylMatrixEnergy A Z) (weylMatrixEnergy U V)
      (scalarNormExpression 0 A Z) (scalarNormExpression 0 U V)
      (traceEnergy A) (traceEnergy U) (blockRadialGradient A Z) (blockRadialGradient U V) =
    (17 / 10 : ℝ) * traceCouplingTerm A U Z V +
      158 * varianceDensity A U (blockRadialGradient A Z) (blockRadialGradient U V) +
      (kappaNormIntegrand A U Z V + kappaNormIntegrand U A V Z) := by
  rw [kappaNormIntegrand_pair]
  unfold scalarCouplingTerm traceCouplingTerm varianceDensity
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

theorem totalEnergyField_apply (d : MetricGreenData g μ) (e : FrameBundle g) :
    d.totalEnergyField e = weylGradientEnergy (plusWeylGradient g e.base e.frame) +
      weylGradientEnergy (minusWeylGradient g e.base e.frame) := by
  have hz : plusWeylGradient g e.base e.frame.reflect =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  change _ + weylGradientEnergy (plusWeylGradient g e.base e.frame.reflect) = _
  rw [hz, reflectedGradient_energy]
  rfl

theorem traceDeficitIntegrand_eq_arrays (d : MetricGreenData g μ)
    (o : OppositeWeylData d) (e : FrameBundle g) :
    d.traceDeficitIntegrand o e = traceCouplingTerm
      (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame) (minusWeylGradient g e.base e.frame) := by
  unfold traceDeficitIntegrand
  rw [d.totalEnergyField_apply, d.jointMatrixEnergy_apply, d.jointTraceEnergy_apply]
  unfold deficitField regularizedDeficit jointScalarNorm
  simp only [ContinuousMap.coe_mk, regularizedBlockNorm_zero]
  unfold traceCouplingTerm
  ring

theorem coupledIntegrand_eq_array (d : MetricGreenData g μ)
    (o : OppositeWeylData d) (e : FrameBundle g) :
    d.coupledIntegrand o e =
      arrayCoupledIntegrand (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) (reflectedGradient (minusWeylGradient g e.base e.frame))
        (weylWeightGradient (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame) (minusWeylGradient g e.base e.frame))
        (reflectedVector (weylWeightGradient (minusWeyl g e.base e.frame) (plusWeyl g e.base e.frame)
          (minusWeylGradient g e.base e.frame) (plusWeylGradient g e.base e.frame)))
        (blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame))
        (blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)) := by
  unfold coupledIntegrand preVarianceIntegrand
  rw [regularizedHessianIntegrand_eq_arrayHessianTerm,
    reflectedHessianIntegrand_eq_arrayHessianTerm, d.traceDeficitIntegrand_eq_arrays]
  unfold arrayCoupledIntegrand
  rw [reflectedGradient_energy, weylMatrixEnergy_reflected, scalarNormExpression_reflected,
    scalarCouplingTerm_eq_trace_and_tests]
  ring

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Apply the finite-array estimate to the actual two Weyl blocks.
The zero faces are supplied by the almost-everywhere derivative theorem. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi QuaternionFrame MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem weylWeightGradient_norm_sq (A U : Mat) (Z V : Angular.Gradient) :
    ‖weylWeightGradient A U Z V‖ ^ 2 =
      (9 / 16 : ℝ) * Energy.scalarWeight (normalizedBlockNorm A) (normalizedBlockNorm U) ^ 2 *
        ‖blockRadialGradient A Z - blockRadialGradient U V‖ ^ 2 := by
  rw [weylWeightGradient_eq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  unfold Energy.scalarWeight
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem MetricGreenData.coupledIntegrand_bound (d : MetricGreenData g μ)
    (o : OppositeWeylData d) [SFinite μ] (hp : ShiftedCurvaturePositive g) :
    ∀ᵐ e ∂μ, d.coupledIntegrand o e ≤
      -couplingCoefficient (d.plusNormField e) (d.minusNormField o e) *
        ((plusRadialEnergy e + minusRadialEnergy e) *
          (plusRadialEnergy e / d.plusNormField e + minusRadialEnergy e / d.minusNormField o e)) +
      2 * Potential.theta (d.plusNormField e) (d.minusNormField o e) *
        (normWeight (d.plusNormField e) * plusRadialEnergy e +
          normWeight (d.minusNormField o e) * minusRadialEnergy e) -
      Potential.theta (d.plusNormField e) (d.minusNormField o e) ^ 2 /
        couplingCoefficient (d.plusNormField e) (d.minusNormField o e) := by
  filter_upwards [d.gradient_zero_ae_on_zero, o.gradient_zero_ae_on_zero] with e he hoe
  let A := plusWeyl g e.base e.frame
  let U := minusWeyl g e.base e.frame
  let Z := plusWeylGradient g e.base e.frame
  let V := minusWeylGradient g e.base e.frame
  have hVs (i) : symmetric (reflectedGradient V i) := by
    intro a b
    change orientationSign i * V i a b = orientationSign i * V i b a
    exact congrArg (fun t : ℝ => orientationSign i * t) ((o.gradientConstraints e).1 i a b)
  have hVt (i) : traceFree (reflectedGradient V i) := by
    change (∑ a, orientationSign i * V i a a) = 0
    rw [← Finset.mul_sum, (o.gradientConstraints e).2 i, mul_zero]
  have hVb (r i) : gradientDivergence (reflectedGradient V) r i = 0 := by
    rw [reflectedGradient_divergence, o.gradientBianchi e, mul_zero]
  have hzero : normalizedBlockNorm A = 0 → Z = 0 := by
    intro h
    exact funext (he ((normalizedBlockNorm_eq_zero_iff A).mp h))
  have hzerob : normalizedBlockNorm U = 0 → reflectedGradient V = 0 := by
    intro h
    have hv : V = 0 := funext (hoe ((normalizedBlockNorm_eq_zero_iff U).mp h))
    funext i
    change orientationSign i • V i = 0
    rw [hv]
    exact smul_zero _
  obtain ⟨x, y, hx, hy, hxy⟩ := hp e
  have ha := weylWeightGradient_norm_sq A U Z V
  have hab : ‖reflectedVector (weylWeightGradient U A V Z)‖ ^ 2 =
      (9 / 16 : ℝ) * Energy.scalarWeight (normalizedBlockNorm U) (normalizedBlockNorm A) ^ 2 *
        ‖blockRadialGradient A Z - blockRadialGradient U V‖ ^ 2 := by
    rw [reflectedVector_norm, weylWeightGradient_norm_sq, norm_sub_rev]
  have h := pointwise_coupling_bound_closed A U Z (reflectedGradient V)
    (weylWeightGradient A U Z V) (reflectedVector (weylWeightGradient U A V Z))
    (blockRadialGradient A Z) (blockRadialGradient U V)
    (d.weyl.symmetric e) (o.symmetric e) (d.weyl.traceFree e) (o.traceFree e)
    (d.gradientConstraints e).1 (d.gradientConstraints e).2 (d.gradientBianchi e)
    hVs hVt hVb hzero hzerob x y hx hy hxy rfl
    (reflectedGradient_radial_norm U V).symm ha hab
  rw [d.coupledIntegrand_eq_array o e]
  simp only [MetricGreenData.plusNormField, MetricGreenData.minusNormField,
    MetricGreenData.plusMatrixMap, MetricGreenData.minusMatrixMap,
    ContinuousMap.coe_mk, plusRadialEnergy, minusRadialEnergy]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem MetricGreenData.radialEnergy_support (d : MetricGreenData g μ)
    (o : OppositeWeylData d) [SFinite μ] :
    ∀ᵐ e ∂μ, (d.plusNormField e = 0 → plusRadialEnergy e = 0) ∧
      (d.minusNormField o e = 0 → minusRadialEnergy e = 0) ∧
      (d.plusNormField e = 1 → plusRadialEnergy e = 0) ∧
      (d.minusNormField o e = 1 → minusRadialEnergy e = 0) := by
  filter_upwards [d.radial_zero_ae_on_level 0, o.radial_zero_ae_on_level 0,
    d.radial_zero_ae_on_level 1, o.radial_zero_ae_on_level 1] with e hp hq hp1 hq1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    simp only [plusRadialEnergy, hp h, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  · intro h
    simp only [minusRadialEnergy, hq h, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  · intro h
    simp only [plusRadialEnergy, hp1 h, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  · intro h
    simp only [minusRadialEnergy, hq1 h, norm_zero, zero_pow (by decide : 2 ≠ 0)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrability of the actual radial difference and the exact variance
correction. The weighted variance inequality remains a separate geometric
obligation; the mean correction is derived from equal second moments. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

include r

theorem radialDifferenceSq_integrable (o : OppositeWeylData d) :
    Integrable (fun e => ‖blockRadialGradient (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame) -
        blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)‖ ^ 2) μ := by
  let p : Fin 4 → FrameBundle g → ℝ := fun i e => regularizedRadialDerivative 0
    (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i)
  let q : Fin 4 → FrameBundle g → ℝ := fun i e => regularizedRadialDerivative 0
    (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame i)
  have hp (i) : AEStronglyMeasurable (p i) μ := (d.radial_integrable i).aestronglyMeasurable
  have hq (i) : AEStronglyMeasurable (q i) μ := (r.opposite_radial_integrable i).aestronglyMeasurable
  have hpp (i) : Integrable (fun e => p i e * p i e) μ :=
    integrable_radialDerivative_product _ _ _ _ (d.continuousGradient i) (d.continuousGradient i)
      (fun e => (d.gradientConstraints e).1 i) (fun e => (d.gradientConstraints e).1 i) (hp i) (hp i)
  have hpq (i) : Integrable (fun e => p i e * q i e) μ :=
    integrable_radialDerivative_product _ _ _ _ (d.continuousGradient i) (o.continuousGradient i)
      (fun e => (d.gradientConstraints e).1 i) (fun e => (o.gradientConstraints e).1 i) (hp i) (hq i)
  have hqq (i) : Integrable (fun e => q i e * q i e) μ :=
    integrable_radialDerivative_product _ _ _ _ (o.continuousGradient i) (o.continuousGradient i)
      (fun e => (o.gradientConstraints e).1 i) (fun e => (o.gradientConstraints e).1 i) (hq i) (hq i)
  have h := integrable_finsetSum Finset.univ (fun i _ =>
    ((hpp i).sub ((hpq i).const_mul 2)).add (hqq i))
  apply h.congr
  filter_upwards [] with e
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Pi.add_apply, Pi.sub_apply, PiLp.sub_apply]
  apply Finset.sum_congr rfl
  intro i _
  change p i e * p i e - 2 * (p i e * q i e) + q i e * q i e = (p i e - q i e) ^ 2
  ring

theorem radialVarianceEnergy_integrable (o : OppositeWeylData d) :
    Integrable (fun e => ‖blockRadialGradient (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame) -
        blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)‖ ^ 2 /
      (4 + normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 +
        normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2)) μ := by
  let K : C(FrameBundle g, ℝ) := ⟨fun e => 1 /
    (4 + d.plusNormField e ^ 2 + d.minusNormField o e ^ 2), by
      apply continuous_const.div
      · fun_prop
      · intro e
        positivity⟩
  have h := integrable_continuous_weight (r.radialDifferenceSq_integrable o) K
  apply h.congr
  filter_upwards [] with e
  simp only [K, MetricGreenData.plusNormField, MetricGreenData.minusNormField,
    MetricGreenData.plusMatrixMap, MetricGreenData.minusMatrixMap, ContinuousMap.coe_mk]
  ring

theorem varianceDensity_integrable (o : OppositeWeylData d) :
    Integrable (fun e => varianceDensity (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame))
      (blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame))) μ := by
  have hc : Continuous (fun e : FrameBundle g =>
      (1 - (2 - d.plusNormField e - d.minusNormField o e) ^ 2 / 4) *
        (d.plusNormField e - d.minusNormField o e) ^ 2) := by fun_prop
  exact (r.radialVarianceEnergy_integrable o).sub
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transfer the reflection-symmetric Green integral to the original
oriented frame measure. The variance correction is then performed on that
original measure, where its scalar means and Weyl gaps have the intended
geometric interpretation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem MetricGreenData.coupledIntegral_oriented (d : MetricGreenData g μ)
    (o : OppositeWeylData d) [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]
    (hparallel : ParallelReflection d) (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2)
    (hsecond : (∫ e, d.plusNormField e ^ 2 ∂μ) = ∫ e, d.minusNormField o e ^ 2 ∂μ)
    (hvariance : (∫ e, (d.plusNormField e - d.minusNormField o e) ^ 2 ∂μ) -
      (∫ e, d.plusNormField e - d.minusNormField o e ∂μ) ^ 2 ≤
      ∫ e, ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) -
        blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)‖ ^ 2 /
        (4 + d.plusNormField e ^ 2 + d.minusNormField o e ^ 2) ∂μ) :
    Integrable (d.coupledIntegrand o) μ ∧ 0 ≤ ∫ e, d.coupledIntegrand o e ∂μ := by
  let oS := o.onSymmetricMeasure hparallel
  let rS := d.symmetricReflection hparallel
  have hF := (integrable_add_measure.mp (rS.radialVarianceEnergy_integrable oS)).1
  have hD := (integrable_add_measure.mp (rS.varianceDensity_integrable oS)).1
  have hpre := d.preVarianceGreen_oriented o hparallel hp hdecomp hpinch
  have hv := Variance.variance_correction_nonneg d.plusNormField (d.minusNormField o) _
    d.plusNormField.continuous (d.minusNormField o).continuous hF hsecond hvariance
  refine ⟨hpre.1.add (hD.const_mul 158), ?_⟩
  change 0 ≤ ∫ e, d.preVarianceIntegrand o e + 158 * varianceDensity _ _ _ _ ∂μ
  rw [integral_add hpre.1 (hD.const_mul 158), integral_const_mul]
  exact add_nonneg hpre.2 (mul_nonneg (by norm_num) hv)

end
end PositiveEinsteinFour.Geometry
end


section

/-! One-block vanishing for the metric under weighted-variance and moment
hypotheses. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

theorem MetricGreenData.one_block_zero_of_variance_oai (d : MetricGreenData g μ)
    (o : OppositeWeylData d) (orientation : FrameOrientation g) (hparallel : ParallelReflection d)
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, d.plusNormField e + d.minusNormField o e < 2)
    (hsecond : (∫ e, d.plusNormField e ^ 2 ∂μ) = ∫ e, d.minusNormField o e ^ 2 ∂μ)
    (hdifference : (∫ e, (d.plusNormField e - d.minusNormField o e) ^ 2 ∂μ) -
      (∫ e, d.plusNormField e - d.minusNormField o e ∂μ) ^ 2 ≤
      ∫ e, ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) -
        blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)‖ ^ 2 /
        (4 + d.plusNormField e ^ 2 + d.minusNormField o e ^ 2) ∂μ)
    (hplus : (∫ e, (d.plusNormField e - ∫ f, d.plusNormField f ∂μ) ^ 2 ∂μ) ≤
      ∫ e, plusRadialEnergy e ∂μ)
    (hminus : (∫ e, (d.minusNormField o e - ∫ f, d.minusNormField o f ∂μ) ^ 2 ∂μ) ≤
      ∫ e, minusRadialEnergy e ∂μ)
    (hgapPlus : (∃ e ∈ orientation.positive, d.plusNormField e ≠ 0) → 1 ≤ ∫ e, d.plusNormField e ^ 2 ∂μ)
    (hgapMinus : (∃ e ∈ orientation.positive, d.minusNormField o e ≠ 0) → 1 ≤ ∫ e, d.minusNormField o e ^ 2 ∂μ) :
    (∀ e ∈ orientation.positive, d.plusNormField e = 0) ∨
      ∀ e ∈ orientation.positive, d.minusNormField o e = 0 := by
  classical
  by_cases hpzero : ∀ e ∈ orientation.positive, d.plusNormField e = 0
  · exact Or.inl hpzero
  by_cases hmzero : ∀ e ∈ orientation.positive, d.minusNormField o e = 0
  · exact Or.inr hmzero
  push Not at hpzero hmzero
  have hvi : Integrable (fun e => (d.plusNormField e - ∫ f, d.plusNormField f ∂μ) ^ 2) μ :=
    ((d.plusNormField.continuous.sub continuous_const).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hbi : Integrable (fun e => (d.minusNormField o e - ∫ f, d.minusNormField o f ∂μ) ^ 2) μ :=
    (((d.minusNormField o).continuous.sub continuous_const).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hI := d.coupledIntegral_oriented o hparallel hp hdecomp hpinch hsecond hdifference
  have hz := one_block_vanishes_of_coupled_bound
    (I := d.coupledIntegrand o)
    (θ := fun e => Potential.theta (d.plusNormField e) (d.minusNormField o e))
    (v := d.plusNormField) (b := d.minusNormField o)
    (p := plusRadialEnergy) (q := minusRadialEnergy)
    hI.1 hI.2
    (Filter.Eventually.of_forall (fun e => normalizedBlockNorm_nonneg _))
    (Filter.Eventually.of_forall (fun e => normalizedBlockNorm_nonneg _))
    (Filter.Eventually.of_forall hpinch)
    (Filter.Eventually.of_forall (fun e => sq_nonneg _))
    (Filter.Eventually.of_forall (fun e => sq_nonneg _))
    (d.radialEnergy_support o) (d.coupledIntegrand_bound o hp)
    hvi hbi hplus hminus (fun _ => hgapPlus hpzero) (fun _ => hgapMinus hmzero)
  rcases hz with hz | hz
  · exact Or.inl (fun e _ => hz e)
  · exact Or.inr (fun e _ => hz e)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

theorem solution.{u_1} : type_of% @OAI.PositiveEinsteinFour.Geometry.MetricGreenData.one_block_zero_of_variance_oai.{u_1} := @OAI.PositiveEinsteinFour.Geometry.MetricGreenData.one_block_zero_of_variance_oai.{u_1}
