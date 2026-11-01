-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.QuaternionFrame.arrayCoupledIntegrand_le_reduced
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:44:45.014091+00:00
-- url     : https://prove2.me/submissions/9431cff5-e829-414f-bb2b-a712506a9bbb

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C016
import Definitions.Def_OAIQ091C018
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_totalPlus_weightPlusPart_generalCost
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_weightPlusPart_plus_energy
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_self
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_general_highestProjection_curvature_le
import Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_highestProjection_plusPolynomial
import Theorems.Thm_OAI_PositiveEinsteinFour_Quadratic_axial_matrix_nonneg
import Theorems.Thm_OAI_PositiveEinsteinFour_quadratic_form_nonneg_of_det

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

theorem radialCoordinate_parameters (S : Shape) (p k l : Vec) :
    radialCoordinate S (parameters S p k l) = p := by
  unfold radialCoordinate parameters
  simp only [smul_sub, smul_smul, Finset.sum_sub_distrib, ← Finset.sum_smul]
  have hs : ∑ i, S.s i * S.s i = 6 := by simpa [pow_two] using S.square
  rw [hs, difference_orthogonal]
  module

theorem secondCoordinate_parameters (S : Shape) (p k l : Vec) :
    secondCoordinate S (parameters S p k l) = k := by
  unfold secondCoordinate parameters
  simp only [smul_sub, smul_smul, Finset.sum_sub_distrib, ← Finset.sum_smul]
  have hc : ∑ i, difference S.s i * S.s i = 0 := by
    simpa [mul_comm] using difference_orthogonal S.s
  have hd : ∑ i, difference S.s i * difference S.s i = 18 := by
    simpa [pow_two] using S.difference_square
  rw [hc, hd]
  module

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HessianAlgebra
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite algebra in the weighted Hessian inequality

These are the energy metric, compressed curvature action, matrix (12), and
sharp scalar optimization in (13). The manifold Hessian and its integration
by parts are separate from these finite-dimensional identities.
-/

namespace PositiveEinsteinFour.HessianAlgebra

noncomputable section

/-- The last scalar maximization in the sharp cubic contraction estimate.
Its hypotheses are precisely the energy spent by the distinguished tangent
component, `e₁ = 5ν²/3 ≤ e`. -/
theorem cubic_energy_optimization {ν e : ℝ}
    (_hν : 0 ≤ ν) (he : (5 / 3) * ν ^ 2 ≤ e) :
    ν * (e - ν ^ 2 / 3) ≤
      (4 / 5) * Real.sqrt (3 / 5) * e * Real.sqrt e := by
  have he0 : 0 ≤ e := le_trans (by positivity) he
  let L := Real.sqrt (3 / 5) * Real.sqrt e
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hL2 : L ^ 2 = (3 / 5) * e := by
    dsimp [L]
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt he0]
  have hνL : ν ≤ L := by nlinarith only [_hν, he, hL2, hL]
  have hνLprod : ν * L ≤ L ^ 2 := by nlinarith
  have hgap : 0 ≤ e - (L ^ 2 + L * ν + ν ^ 2) / 3 := by nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr hνL) hgap
  have hL3 : L ^ 3 = (3 / 5) * e * L := by rw [pow_succ, hL2]
  calc
    _ ≤ (4 / 5) * L * e := by nlinarith
    _ = _ := by dsimp [L]; ring

/-- The mixed radial/defect cost is controlled by an explicit square. The
statement retains the actual tangent inner products. -/
theorem projection_bracket_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v y σ ρ : ℝ} (hv : 0 ≤ v) (hσ : σ ≤ 1) (p k l : E) :
    (7 / 12) * (4 + y) * ((5 / 3) * ‖p‖ ^ 2 + 5 * ‖k‖ ^ 2 + ‖l‖ ^ 2) -
      (5 / 4) * v * ((4 / 3) * σ * ‖p‖ ^ 2 -
        8 * ρ / Real.sqrt 3 * inner ℝ p k - 4 * σ * ‖k‖ ^ 2 - 2 * inner ℝ k l) ≤
    QuarticEnergy.projectionCoefficient v y σ ρ * ((5 / 3) * ‖p‖ ^ 2) +
      Energy.defectCoefficient v y * (5 * ‖k‖ ^ 2 + ‖l‖ ^ 2) := by
  have hpure : 0 ≤ v * ((5 / 4) * ‖l - k‖ ^ 2 + 5 * (1 - σ) * ‖k‖ ^ 2) := by
    positivity
  have hmix : 0 ≤ 5 * ‖(ρ * v / (2 * Real.sqrt 3)) • p - (2 : ℝ) • k‖ ^ 2 := by
    positivity
  have hl : 0 ≤ 4 * ‖l‖ ^ 2 := by positivity
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right] at hpure hmix
  rw [show inner ℝ l k = inner ℝ k l from real_inner_comm k l] at hpure
  unfold QuarticEnergy.projectionCoefficient Energy.defectCoefficient
  have hidentity :
      QuarticEnergy.projectionCoefficient v y σ ρ * ((5 / 3) * ‖p‖ ^ 2) +
        Energy.defectCoefficient v y * (5 * ‖k‖ ^ 2 + ‖l‖ ^ 2) -
      ((7 / 12) * (4 + y) * ((5 / 3) * ‖p‖ ^ 2 + 5 * ‖k‖ ^ 2 + ‖l‖ ^ 2) -
        (5 / 4) * v * ((4 / 3) * σ * ‖p‖ ^ 2 -
          8 * ρ / Real.sqrt 3 * inner ℝ p k - 4 * σ * ‖k‖ ^ 2 - 2 * inner ℝ k l)) =
      v * ((5 / 4) * (‖l‖ ^ 2 - 2 * inner ℝ k l + ‖k‖ ^ 2) +
        5 * (1 - σ) * ‖k‖ ^ 2) +
      5 * ((ρ * v / (2 * Real.sqrt 3)) ^ 2 * ‖p‖ ^ 2 -
        2 * (ρ * v / (2 * Real.sqrt 3)) * 2 * inner ℝ p k + 4 * ‖k‖ ^ 2) +
      4 * ‖l‖ ^ 2 := by
    unfold QuarticEnergy.projectionCoefficient Energy.defectCoefficient
    field_simp [hne]
    ring_nf
    rw [hsqrt]
    ring
  unfold QuarticEnergy.projectionCoefficient Energy.defectCoefficient at hidentity
  linarith

end
end PositiveEinsteinFour.HessianAlgebra

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_BianchiCurvature
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix
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

/-- This is the contraction of the actual three-by-three matrix, not an
independent scalar surrogate. -/
theorem curvatureContraction_eq_matrix (S : Shape) (v : ℝ) (T : Tensor) :
    curvatureContraction S v T = (v / 6) * ∑ i, ∑ j, S.s i * ‖T.matrix i j‖ ^ 2 := by
  have ht := S.trace
  simp [Fin.sum_univ_succ] at ht
  unfold curvatureContraction
  simp [Tensor.matrix, Fin.sum_univ_succ]
  left
  linear_combination
    -(‖T.off 0‖ ^ 2 + ‖T.off 1‖ ^ 2 + ‖T.off 2‖ ^ 2) * ht

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

/-- The projected quadratic cost is bounded by the exact coefficients used in
equation (19) for the concrete Bianchi tensor. -/
theorem projection_cost_coefficients (S : Shape) {v : ℝ} (hv : 0 ≤ v)
    (y : ℝ) (p k l : Vec) :
    (7 / 12) * (4 + y) * ((parameters S p k l).squaredNorm / 6) -
      (5 / 4) * curvatureContraction S v (parameters S p k l) ≤
    QuarticEnergy.projectionCoefficient v y S.sigma S.rho * ((5 / 3) * ‖p‖ ^ 2) +
      Energy.defectCoefficient v y * ((parameters S p k l).squaredNorm / 6 -
        (5 / 3) * ‖p‖ ^ 2) := by
  have hs : S.sigma ≤ 1 := by nlinarith [S.sigma_rho_circle, sq_nonneg S.rho]
  rw [parameters_energy, curvatureContraction_parameters]
  first | (convert HessianAlgebra.projection_bracket_bound (y := y) (ρ := S.rho) hv hs p k l using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((HessianAlgebra.projection_bracket_bound (y := y) (ρ := S.rho) hv hs p k l).trans (le_of_eq (by ring)))

private theorem binary_inner_nonneg (r h s : ℝ) (hr : 0 ≤ r) (hh : 0 ≤ h)
    (hd : s ^ 2 ≤ r * h) (p k : Vec) :
    0 ≤ r * ‖p‖ ^ 2 + 2 * s * inner ℝ p k + h * ‖k‖ ^ 2 := by
  have hi := abs_real_inner_le_norm p k
  by_cases hs : 0 ≤ s
  · have hform := quadratic_form_nonneg_of_det r h s hr hh hd ‖p‖ (-‖k‖)
    have hcross := mul_le_mul_of_nonneg_left (abs_le.mp hi).1 (show 0 ≤ 2 * s by positivity)
    nlinarith only [hform, hcross]
  · have hform := quadratic_form_nonneg_of_det r h s hr hh hd ‖p‖ ‖k‖
    have hcross := mul_le_mul_of_nonpos_left (abs_le.mp hi).2 (show 2 * s ≤ 0 by linarith)
    nlinarith only [hform, hcross]

/-- The unit normalized matrix-slot action is a contraction for the complete
Bianchi energy metric. -/
theorem normalized_curvature_bound (S : Shape) (p k l : Vec) :
    |(4 / 3) * S.sigma * ‖p‖ ^ 2 - 8 * S.skewMoment * inner ℝ p k -
      4 * S.sigma * ‖k‖ ^ 2 - 2 * inner ℝ k l| ≤
      (5 / 3) * ‖p‖ ^ 2 + 5 * ‖k‖ ^ 2 + ‖l‖ ^ 2 := by
  have hc := S.sigma_skew_circle
  have hslo : -1 ≤ S.sigma := by nlinarith [sq_nonneg S.skewMoment]
  have hshi : S.sigma ≤ 1 := by nlinarith [sq_nonneg S.skewMoment]
  have hminus := binary_inner_nonneg ((5 - 4 * S.sigma) / 3) (4 + 4 * S.sigma)
    (4 * S.skewMoment) (by linarith) (by linarith) (by nlinarith) p k
  have hplus := binary_inner_nonneg ((5 + 4 * S.sigma) / 3) (4 - 4 * S.sigma)
    (-4 * S.skewMoment) (by linarith) (by linarith) (by nlinarith) p k
  have hlminus := sq_nonneg ‖l - k‖
  have hlplus := sq_nonneg ‖l + k‖
  rw [norm_sub_sq_real, real_inner_comm k l] at hlminus
  rw [norm_add_sq_real, real_inner_comm k l] at hlplus
  apply abs_le.mpr
  constructor <;> linarith

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_BianchiCubic
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The sharp cubic contraction in a normalized diagonal frame

The contraction is defined from the actual symmetric matrix of four-vectors.
The displayed diagonal-frame hypothesis is the pointwise spectral-frame
condition used in the curvature calculation, and is not a differential-geometric input.
-/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators

/-- The distinguished tangent component loses one fifth of its energy in
this quadratic contraction. The other components retain the full bound. -/
theorem distinguished_component_bound (S : Shape) (a p k l : Vec) (ν : ℝ)
    (ha : ‖a‖ = 1) (hap : inner ℝ a p = ν) (hak : inner ℝ a k = 0) :
    |normalizedCurvatureForm S p k l| ≤
      (5 / 3) * ‖p‖ ^ 2 + 5 * ‖k‖ ^ 2 + ‖l‖ ^ 2 - ν ^ 2 / 3 := by
  let u := p - ν • a
  have hup : ‖p‖ ^ 2 = ν ^ 2 + ‖u‖ ^ 2 := by
    have hu : ‖u‖ ^ 2 = ‖p‖ ^ 2 - ν ^ 2 := by
      dsimp [u]
      rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        real_inner_smul_right, real_inner_comm a p, hap, ha]
      ring
    linarith
  have huk : inner ℝ p k = inner ℝ u k := by
    dsimp [u]
    rw [inner_sub_left, real_inner_smul_left, hak]
    ring
  have hform : normalizedCurvatureForm S p k l = (4 / 3) * S.sigma * ν ^ 2 + normalizedCurvatureForm S u k l := by
    unfold normalizedCurvatureForm
    rw [hup, huk]
    ring
  have hs : |S.sigma| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [S.sigma_skew_circle, sq_nonneg S.skewMoment]
  have hrad : |(4 / 3) * S.sigma * ν ^ 2| ≤ (4 / 3) * ν ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3), abs_of_nonneg (sq_nonneg ν)]
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg ν)]
  have hrest : |normalizedCurvatureForm S u k l| ≤ (5 / 3) * ‖u‖ ^ 2 + 5 * ‖k‖ ^ 2 + ‖l‖ ^ 2 :=
    normalized_curvature_bound S u k l
  rw [hform]
  calc
    _ ≤ |(4 / 3) * S.sigma * ν ^ 2| + |normalizedCurvatureForm S u k l| := abs_add_le _ _
    _ ≤ (4 / 3) * ν ^ 2 + ((5 / 3) * ‖u‖ ^ 2 + 5 * ‖k‖ ^ 2 + ‖l‖ ^ 2) := add_le_add hrad hrest
    _ = _ := by rw [hup]; ring

/-- In the diagonalizing frame for `Z_a`, the cubic contraction is the
normalized matrix-slot quadratic contraction times its scale. -/
theorem cubicContraction_diagonal (S : Shape) (a : Vec) (T : Tensor) (ν : ℝ)
    (hdiag : ∀ i j, inner ℝ a (T.matrix i j) = if i = j then ν * S.s i else 0) :
    cubicContraction a T = ν * curvatureContraction S 1 T := by
  have hsum (i j : Fin 3) :
      (∑ k, inner ℝ a (T.matrix i j) * inner ℝ (T.matrix j k) (T.matrix k i)) =
        if i = j then ν * S.s i * ∑ k, ‖T.matrix i k‖ ^ 2 else 0 := by
    by_cases hij : i = j
    · subst j
      rw [hdiag]
      simp only [ite_true, if_true]
      have hinner (k : Fin 3) :
          inner ℝ (T.matrix i k) (T.matrix k i) = ‖T.matrix i k‖ ^ 2 := by
        rw [T.matrix_symmetric k i, real_inner_self_eq_norm_sq]
      simp_rw [hinner]
      rw [Finset.mul_sum]
    · simp [hdiag, hij]
  unfold cubicContraction
  simp_rw [hsum]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  rw [curvatureContraction_eq_matrix]
  simp only [Fin.sum_univ_succ]
  ring

/-- The diagonal-frame condition determines the radial and orthogonal
components along the chosen tangent direction. -/
theorem diagonal_parameter_components (S : Shape) (a p k l : Vec) (ν : ℝ)
    (hdiag : ∀ i j, inner ℝ a ((parameters S p k l).matrix i j) =
      if i = j then ν * S.s i else 0) :
    inner ℝ a p = ν ∧ inner ℝ a k = 0 := by
  have hd (i : Fin 3) : inner ℝ a ((parameters S p k l).diagonal i) = ν * S.s i := by
    have h := hdiag i i
    have hm : (parameters S p k l).matrix i i = (parameters S p k l).diagonal i := by
      fin_cases i <;> rfl
    simpa only [hm, ite_true, if_true] using h
  constructor
  · rw [← radialCoordinate_parameters S p k l]
    unfold radialCoordinate
    simp only [real_inner_smul_right, inner_sum]
    simp_rw [hd]
    have hsum : ∑ i, S.s i * (ν * S.s i) = ν * ∑ i, S.s i ^ 2 := by
      simp only [Fin.sum_univ_succ]
      ring
    rw [hsum, S.square]
    ring
  · rw [← secondCoordinate_parameters S p k l]
    unfold secondCoordinate
    simp only [real_inner_smul_right, inner_sum]
    simp_rw [hd]
    have hsum : ∑ i, difference S.s i * (ν * S.s i) = ν * ∑ i, S.s i * difference S.s i := by
      simp only [Fin.sum_univ_succ]
      ring
    rw [hsum, difference_orthogonal]
    ring

/-- The sharp constant in (13), proved from the actual tensor contraction in
any normalized diagonal frame for the distinguished derivative. -/
theorem cubicContraction_sharp_diagonal (S : Shape) (a p k l : Vec) {ν : ℝ}
    (ha : ‖a‖ = 1) (hν : 0 ≤ ν)
    (hdiag : ∀ i j, inner ℝ a ((parameters S p k l).matrix i j) =
      if i = j then ν * S.s i else 0) :
    |cubicContraction a (parameters S p k l)| ≤
      (4 / 5) * Real.sqrt (3 / 5) * ((parameters S p k l).squaredNorm / 6) *
        Real.sqrt ((parameters S p k l).squaredNorm / 6) := by
  obtain ⟨hap, hak⟩ := diagonal_parameter_components S a p k l ν hdiag
  have hbound := distinguished_component_bound S a p k l ν ha hap hak
  have he : (5 / 3) * ν ^ 2 ≤ (5 / 3) * ‖p‖ ^ 2 + 5 * ‖k‖ ^ 2 + ‖l‖ ^ 2 := by
    have hp : ν ^ 2 ≤ ‖p‖ ^ 2 := by
      have hi := abs_real_inner_le_norm a p
      rw [ha, one_mul, hap] at hi
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg ν) (norm_nonneg p)).2 hi
    nlinarith [sq_nonneg ‖k‖, sq_nonneg ‖l‖]
  rw [cubicContraction_diagonal S a _ ν hdiag, curvatureContraction_parameters,
    parameters_energy]
  have hr : 8 * S.rho / Real.sqrt 3 = 8 * S.skewMoment := by
    rw [mul_div_assoc, S.rho_div_sqrt_three]
  rw [hr]
  simp only [one_mul]
  change |ν * normalizedCurvatureForm S p k l| ≤ _
  rw [abs_mul, abs_of_nonneg hν]
  calc
    _ ≤ ν * ((5 / 3) * ‖p‖ ^ 2 + 5 * ‖k‖ ^ 2 + ‖l‖ ^ 2 - ν ^ 2 / 3) :=
      mul_le_mul_of_nonneg_left hbound hν
    _ ≤ _ := HessianAlgebra.cubic_energy_optimization hν he

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceHessian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_3 _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prescribed trace component of the Bianchi Hessian

The arrays are real tensors. The lift is the explicit formula for the
restricted trace adjoint in Section 5; its Bianchi constraint, trace and
squared norm follow by direct calculation in the fixed quaternion frame. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators
open Bianchi

/-- The spin-two Casimir, computed on the actual symmetric trace-free matrix. -/
theorem matrixAction_casimir (M : Mat) (hs : symmetric M) (ht : traceFree M) :
    (∑ a, ∑ b, ∑ s, matrixAction s M a b ^ 2) = 24 * matrixNormSq M := by
  rw [← coordinates_eq M hs ht]
  simp [matrixAction, rotation, ofCoordinates, matrixNormSq,
    Fin.sum_univ_succ]
  ring

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientCasimir
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_3 _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Bianchi coupling operator on first derivatives. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

/-- Quaternion multiplication preserves the full Euclidean inner product. -/
theorem quaternion_inner (s : Fin 3) (p q : Vec) :
    inner ℝ (quaternion s p) (quaternion s q) = inner ℝ p q := by
  have h := quaternion_norm_sq s (p + q)
  rw [quaternion_add, norm_add_sq_real, norm_add_sq_real,
    quaternion_norm_sq, quaternion_norm_sq] at h
  linarith

/-- The infinitesimal quaternion action is skew-adjoint. -/
theorem quaternion_inner_skew (s : Fin 3) (p q : Vec) :
    inner ℝ (quaternion s p) q = -inner ℝ p (quaternion s q) := by
  have h := quaternion_inner s p (quaternion s q)
  rw [quaternion_square, inner_neg_right] at h
  linarith

private theorem rotate_sums (f : Fin 3 → Fin 3 → Fin 3 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ s, ∑ u, f a b s u) = ∑ u, ∑ a, ∑ b, ∑ s, f a b s u := by
  calc
    _ = ∑ a, ∑ b, ∑ u, ∑ s, f a b s u := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ u, ∑ b, ∑ s, f a b s u := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

private theorem matrixRotation_component (s : Fin 3) (Z : Tensor)
    (a b : Fin 3) (u : Fin 4) :
    matrixRotation s Z a b u = matrixAction s (fun a b => Z.matrix a b u) a b := by
  simp [matrixRotation, matrixAction, Finset.sum_sub_distrib,
    Fin.sum_univ_succ]
  ring

/-- The matrix-spin Casimir on the actual four-vector-valued tensor. -/
theorem matrixRotation_energy (Z : Tensor) (hz : Z.traceFree) :
    (∑ a, ∑ b, ∑ s, ‖matrixRotation s Z a b‖ ^ 2) = 24 * Z.squaredNorm := by
  let M (u : Fin 4) : Mat := fun a b => Z.matrix a b u
  have hs (u : Fin 4) : symmetric (M u) := by
    intro a b
    exact congrArg (fun q : Vec => q u) (Z.matrix_symmetric a b)
  have ht (u : Fin 4) : traceFree (M u) := by
    have h := congrArg (fun q : Vec => q u) hz
    simpa [traceFree, M, Tensor.traceFree, Tensor.matrix, Fin.sum_univ_succ] using h
  have hc (u : Fin 4) := matrixAction_casimir (M u) (hs u) (ht u)
  have hr : (∑ u : Fin 4, ∑ a, ∑ b, Z.matrix a b u ^ 2) = Z.squaredNorm := by
    unfold Tensor.squaredNorm
    simp only [EuclideanSpace.real_norm_sq_eq]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  simp only [EuclideanSpace.real_norm_sq_eq]
  rw [rotate_sums]
  simp_rw [matrixRotation_component]
  change (∑ u : Fin 4, ∑ a, ∑ b, ∑ s, matrixAction s (M u) a b ^ 2) = _
  simp_rw [hc]
  simp only [matrixNormSq, M, ← Finset.mul_sum]
  rw [hr]

/-- The Bianchi gradient has the exact inner Casimir energy 35. -/
theorem gradientGenerator_energy (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ a, ∑ b, ∑ s, ‖gradientGenerator s Z a b‖ ^ 2) = 35 * Z.squaredNorm := by
  have hi : (∑ a, ∑ b, ∑ s : Fin 3, ‖quaternion s (Z.matrix a b)‖ ^ 2) =
      3 * Z.squaredNorm := by
    simp [Tensor.squaredNorm, Fin.sum_univ_succ]
    ring
  have he (a b : Fin 3) :
      (∑ s, inner ℝ (quaternion s (Z.matrix a b)) (matrixRotation s Z a b)) =
        4 * ‖Z.matrix a b‖ ^ 2 := by
    simp only [quaternion_inner_skew, Finset.sum_neg_distrib]
    rw [← inner_sum]
    change -inner ℝ (Z.matrix a b) (gradientCoupling Z a b) = _
    rw [gradientCoupling_eq Z hb]
    simp [real_inner_smul_right]
  have hx : (∑ a, ∑ b, ∑ s,
      inner ℝ (quaternion s (Z.matrix a b)) (matrixRotation s Z a b)) =
      4 * Z.squaredNorm := by
    simp_rw [he]
    simp only [← Finset.mul_sum, Tensor.squaredNorm]
  have hr := matrixRotation_energy Z hz
  have hsplit : (∑ a, ∑ b, ∑ s, ‖gradientGenerator s Z a b‖ ^ 2) =
      (∑ a, ∑ b, ∑ s : Fin 3, ‖quaternion s (Z.matrix a b)‖ ^ 2) +
      (∑ a, ∑ b, ∑ s, ‖matrixRotation s Z a b‖ ^ 2) +
      2 * (∑ a, ∑ b, ∑ s,
        inner ℝ (quaternion s (Z.matrix a b)) (matrixRotation s Z a b)) := by
    simp only [gradientGenerator, norm_add_sq_real, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    ring
  rw [hsplit, hi, hr, hx]
  ring

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TensorPairing
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Skew matrix actions on the actual four tensor slots. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators

theorem matrixAction_row_sum (s : Fin 3) (M : Mat) (a b : Fin 3) :
    matrixAction s M a b = (∑ c, rotation s a c * M c b) +
      ∑ c, rotation s b c * M a c := by
  unfold matrixAction
  simp only [Finset.sum_sub_distrib]
  have h (c : Fin 3) : M a c * rotation s c b = -(rotation s b c * M a c) := by
    rw [rotation_skew s c b]
    ring
  simp_rw [h]
  rw [Finset.sum_neg_distrib]
  ring

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CoupledOperator
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.QuaternionFrame.fieldRaw_rawField _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual real coupled operator used for the plus projection. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- Entrywise kernel reduction to the two actual slot actions. -/
theorem coupledOperator_apply (X : Hessian) (i j : Fin 4) (a b : Fin 3) :
    coupledOperator X i j a b = ∑ s : Fin 3, ∑ k : Fin 4,
      quaternionMatrix s i k * ((∑ l : Fin 4, quaternionMatrix s j l * X k l a b) +
        matrixAction s (X k j) a b) := by
  simp only [coupledOperator, couplingKernel, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp [Fintype.sum_prod_type, tensorCoordinates, matrixAction_row_sum,
    add_mul, mul_add, Finset.sum_add_distrib,
    ite_mul, mul_ite, ite_and, Finset.mul_sum]
  ring_nf

/-- The actual coupled operator on a real rank-one tensor. -/
theorem coupledOperator_rawWeight (a : Vec) (Z : RawGradient) :
    coupledOperator (rawWeight a Z) =
      ∑ s : Fin 3, rawWeight (quaternion s a) (rawGradientGenerator s Z) := by
  funext i j b c
  simp only [Fin.sum_univ_three, Pi.add_apply, Matrix.add_apply, rawWeight]
  change coupledOperator (rawWeight a Z) i j b c =
    quaternion 0 a i * rawGradientGenerator 0 Z b c j +
    quaternion 1 a i * rawGradientGenerator 1 Z b c j +
    quaternion 2 a i * rawGradientGenerator 2 Z b c j
  rw [coupledOperator_apply]
  have ha (s : Fin 3) := quaternionMatrix_apply s a i
  have hZ (s : Fin 3) := quaternionMatrix_apply s (Z b c) j
  simp only [Fin.sum_univ_four] at ha hZ
  simp [rawWeight, matrixAction, rawGradientGenerator, rawMatrixRotation,
    Fin.sum_univ_three, Fin.sum_univ_four]
  rw [← ha 0, ← ha 1, ← ha 2, ← hZ 0, ← hZ 1, ← hZ 2]
  ring

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CubicWeight
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the actual cubic trace and its squared-weight contribution. -/

namespace PositiveEinsteinFour.Bianchi

open scoped BigOperators
open TraceHessian

noncomputable section

private theorem derivative_trace (T : Tensor) (d : Fin 4) :
    Matrix.trace (derivativeMatrix T d *
      (∑ j, derivativeMatrix T j * derivativeMatrix T j)) =
      ∑ i, ∑ j, ∑ k, T.matrix i j d * inner ℝ (T.matrix j k) (T.matrix k i) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sum_apply,
    derivativeMatrix, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro d' _
  ring

/-- The coordinate contraction and the actual matrix trace have exactly
the normalization used in the weighted Green formula. -/
theorem weightedCubicTrace_eq (a : Vec) (T : Tensor) :
    weightedCubicTrace a T = 6 * cubicContraction a T := by
  unfold weightedCubicTrace
  simp_rw [derivative_trace]
  simp only [Finset.mul_sum]
  calc
    _ = ∑ i : Fin 3, ∑ d : Fin 4, ∑ j : Fin 3, ∑ k : Fin 3,
        a d * (T.matrix i j d * inner ℝ (T.matrix j k) (T.matrix k i)) :=
      Finset.sum_comm
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ d : Fin 4,
        a d * (T.matrix i j d * inner ℝ (T.matrix j k) (T.matrix k i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        inner ℝ a (T.matrix i j) * inner ℝ (T.matrix j k) (T.matrix k i) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      have ha : inner ℝ a (T.matrix i j) = ∑ d, a d * T.matrix i j d := by
        simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
        apply Finset.sum_congr rfl
        intro d _
        ring
      rw [ha, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = _ := by unfold cubicContraction; ring

/-- The sharp diagonal-frame estimate applies to every actual Bianchi
tensor, by the proved reconstruction of its three vector coordinates. -/
theorem cubicContraction_sharp_tensor_diagonal (S : Shape) (a : Vec) (T : Tensor)
    (ht : T.traceFree) (hb : T.bianchi) {ν : ℝ}
    (ha : ‖a‖ = 1) (hν : 0 ≤ ν)
    (hdiag : ∀ i j, inner ℝ a (T.matrix i j) = if i = j then ν * S.s i else 0) :
    |cubicContraction a T| ≤
      (4 / 5) * Real.sqrt (3 / 5) * (T.squaredNorm / 6) *
        Real.sqrt (T.squaredNorm / 6) := by
  have hrec := parameters_reconstruction S T ht hb
  rw [← hrec] at hdiag ⊢
  exact cubicContraction_sharp_diagonal S a _ _ _ ha hν hdiag

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates00
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The finite matrix certificates for the quadratic coupling estimate. -/

namespace PositiveEinsteinFour.Quadratic

open Potential

noncomputable section

/-- The exact matrix monotonicity identity used to move away from the axial
spectral value. Its remainder is a square and a nonnegative diagonal term. -/
theorem spectral_matrix_identity (v b σ x y : ℝ) :
    A11 v b σ * x ^ 2 + 2 * A12 v b σ * x * y + A22 v b σ * y ^ 2 =
      (A11 v b 1 * x ^ 2 + 2 * A12 v b 1 * x * y + A22 v b 1 * y ^ 2) +
      (1 - σ) * v ^ 2 * ((51 * v * x - Pl v b * y) ^ 2 +
        (51 / 5) * v * P0 v b * y ^ 2) := by
  unfold A11 A12 A22 K1 K2 K12 P0 Pk Pl
  ring

/-- The full matrix inequality (21) for every spectral value `σ ≤ 1`.
The lower bound `-1 ≤ σ` is needed later for the Schur complement, but
is not needed for this monotonicity implication. -/
theorem spectral_matrix_nonneg {v b σ : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hsum : v + b ≤ 2) (hσ : σ ≤ 1) (x y : ℝ) :
    0 ≤ A11 v b σ * x ^ 2 + 2 * A12 v b σ * x * y + A22 v b σ * y ^ 2 := by
  have hbase := axial_matrix_nonneg hv hb hsum x y
  have hd : 0 ≤ 2 - v - b := by linarith
  have hw : 0 ≤ weight v b := sq_nonneg _
  have hp0 : 0 ≤ P0 v b := by unfold P0 Pk; positivity
  rw [spectral_matrix_identity]
  exact add_nonneg hbase (by positivity)

end

end PositiveEinsteinFour.Quadratic
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors00
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-!
# The axial reduction of the quadratic coupling terms

The exact matrix certificate (21) implies the full three-variable quadratic
inequality. The proof multiplies by the positive `P0 * v` and applies the
closed two-by-two determinant criterion, so it also covers the axial endpoint.
-/

namespace PositiveEinsteinFour

open Quadratic Potential

noncomputable section

/-- The spectral Schur completion, including `σ = 1`. -/
theorem spectral_schur_nonneg
    (v P σ ρ D W p : ℝ)
    (hv : 0 < v) (hP : 0 < P)
    (hσlower : -1 ≤ σ) (hσupper : σ ≤ 1)
    (hcircle : ρ ^ 2 = 1 - σ ^ 2)
    (hA : 0 ≤ P * v * D - (1 + σ) * v ^ 2 * W ^ 2) :
    0 ≤ (1 - σ) * v * P / 3 * p ^ 2 -
      2 * v * ρ / Real.sqrt 3 * p * W + D := by
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hdet : (-P * ρ / Real.sqrt 3) ^ 2 =
      ((1 - σ) * P ^ 2 / 3) * (1 + σ) := by
    rw [div_pow, hsqrt]
    calc
      (-P * ρ) ^ 2 / 3 = P ^ 2 * ρ ^ 2 / 3 := by ring
      _ = ((1 - σ) * P ^ 2 / 3) * (1 + σ) := by rw [hcircle]; ring
  have hσgap : 0 ≤ 1 - σ := by linarith
  have hsmall := quadratic_form_nonneg_of_det
    ((1 - σ) * P ^ 2 / 3) (1 + σ) (-P * ρ / Real.sqrt 3)
    (by positivity) (by linarith) (le_of_eq hdet) p W
  have hscaled : 0 ≤ v ^ 2 *
      (((1 - σ) * P ^ 2 / 3) * p ^ 2 +
        2 * (-P * ρ / Real.sqrt 3) * p * W + (1 + σ) * W ^ 2) :=
    mul_nonneg (sq_nonneg v) hsmall
  have hidentity :
      P * v * ((1 - σ) * v * P / 3 * p ^ 2 -
        2 * v * ρ / Real.sqrt 3 * p * W + D) =
      (P * v * D - (1 + σ) * v ^ 2 * W ^ 2) +
        v ^ 2 * (((1 - σ) * P ^ 2 / 3) * p ^ 2 +
          2 * (-P * ρ / Real.sqrt 3) * p * W + (1 + σ) * W ^ 2) := by ring
  have hproduct : 0 ≤ P * v * ((1 - σ) * v * P / 3 * p ^ 2 -
      2 * v * ρ / Real.sqrt 3 * p * W + D) := by
    rw [hidentity]
    exact add_nonneg hA hscaled
  exact nonneg_of_mul_nonneg_right hproduct (mul_pos hP hv)

/-- Polynomial-matrix form (21) is the numerator of the Schur complement. -/
theorem spectral_matrix_as_schur (v b σ k l : ℝ) (hv : v ≠ 0) :
    A11 v b σ * k ^ 2 + 2 * A12 v b σ * k * l + A22 v b σ * l ^ 2 =
      P0 v b * v * lowerBlock v b σ k l -
        (1 + σ) * v ^ 2 * (Pk v b * k + Pl v b * l) ^ 2 := by
  unfold A11 A12 A22 lowerBlock
  field_simp [hv]
  ring

/-- The loss from moving off the axial spectral shape is nonnegative, for all
first-derivative variables. This is the quadratic axial reduction in Section 6.
The closed domain and `σ = 1` are included. -/
theorem axial_reduction_nonneg
    {v b σ ρ : ℝ} (hv : 0 < v) (hb : 0 ≤ b) (hsum : v + b ≤ 2)
    (hσlower : -1 ≤ σ) (hσupper : σ ≤ 1) (hcircle : ρ ^ 2 = 1 - σ ^ 2)
    (p k l : ℝ) :
    0 ≤ (1 - σ) * v * P0 v b / 3 * p ^ 2 -
      2 * v * ρ / Real.sqrt 3 * p * (Pk v b * k + Pl v b * l) +
        lowerBlock v b σ k l := by
  have hd : 0 ≤ 2 - v - b := by linarith
  have hw : 0 ≤ weight v b := sq_nonneg _
  have hP : 0 < P0 v b := by
    unfold P0 Pk
    positivity
  apply spectral_schur_nonneg v (P0 v b) σ ρ (lowerBlock v b σ k l)
    (Pk v b * k + Pl v b * l) p hv hP hσlower hσupper hcircle
  rw [← spectral_matrix_as_schur v b σ k l (ne_of_gt hv)]
  exact spectral_matrix_nonneg hv.le hb hsum hσupper k l

end
end PositiveEinsteinFour
end


section

/-! The scalar axial completion is applied coordinatewise to the actual
four-dimensional tangent vectors, retaining all mixed inner products. -/

namespace PositiveEinsteinFour

open scoped BigOperators
open Quadratic Potential Bianchi

noncomputable section

/-- Equation (21) controls the complete tangent-vector quadratic form. -/
theorem axial_reduction_vectors
    {v b σ ρ : ℝ} (hv : 0 < v) (hb : 0 ≤ b) (hsum : v + b ≤ 2)
    (hσlower : -1 ≤ σ) (hσupper : σ ≤ 1) (hcircle : ρ ^ 2 = 1 - σ ^ 2)
    (p k l : Vec) :
    0 ≤ (1 - σ) * v * P0 v b / 3 * ‖p‖ ^ 2 -
      2 * v * ρ / Real.sqrt 3 *
        (Pk v b * inner ℝ p k + Pl v b * inner ℝ p l) +
      (K1 v b σ - 5 * kappa v b / v) * ‖k‖ ^ 2 +
      2 * K12 v b σ * inner ℝ k l +
      (K2 v b σ - kappa v b / v) * ‖l‖ ^ 2 := by
  have hn := Finset.sum_nonneg (s := Finset.univ) (fun i _ =>
    axial_reduction_nonneg hv hb hsum hσlower hσupper hcircle (p i) (k i) (l i))
  have hs (i : Fin 4) :
      (1 - σ) * v * P0 v b / 3 * (p i) ^ 2 -
        2 * v * ρ / Real.sqrt 3 * p i * (Pk v b * k i + Pl v b * l i) +
        lowerBlock v b σ (k i) (l i) =
      (1 - σ) * v * P0 v b / 3 * (p i) ^ 2 -
        2 * v * ρ / Real.sqrt 3 *
          (Pk v b * (k i * p i) + Pl v b * (l i * p i)) +
        (K1 v b σ - 5 * kappa v b / v) * (k i) ^ 2 +
        2 * K12 v b σ * (l i * k i) +
        (K2 v b σ - kappa v b / v) * (l i) ^ 2 := by
    unfold lowerBlock
    ring
  simp_rw [hs] at hn
  simpa only [EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_add, mul_assoc] using hn

private theorem hessian_quadratic_axial_identity (S : Shape) (v b τ : ℝ)
    (p k l : Vec) (hv : v ≠ 0) :
    (axialCoefficient v b + 2 * kappa v b / (3 * v)) * ‖p‖ ^ 2 -
        hessianQuadraticContribution S v b τ p k l =
      ((1 - S.sigma) * v * P0 v b / 3 * ‖p‖ ^ 2 +
        2 * v * S.rho / Real.sqrt 3 *
          (Pk v b * inner ℝ p k + Pl v b * inner ℝ p l) +
        (K1 v b S.sigma - 5 * kappa v b / v) * ‖k‖ ^ 2 +
        2 * K12 v b S.sigma * inner ℝ k l +
        (K2 v b S.sigma - kappa v b / v) * ‖l‖ ^ 2) +
      (51 / 5 : ℝ) * (1 - τ) * b ^ 2 * ((parameters S p k l).squaredNorm / 6) := by
  unfold hessianQuadraticContribution
  rw [hessianTensor_matrix, parameters_energy, curvatureContraction_parameters]
  unfold axialCoefficient P0 Pk Pl K1 K2 K12
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsq : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp [hv, hsq]
  ring_nf
  rw [hsqrt]
  ring

/-- The full quadratic contribution is bounded by its axial value, with
all three derivative variables still actual tangent vectors. -/
theorem hessian_quadratic_axial_bound (S : Shape) {v b τ : ℝ}
    (hv : 0 < v) (hb : 0 ≤ b) (hsum : v + b ≤ 2) (hτ : τ ≤ 1)
    (p k l : Vec) :
    hessianQuadraticContribution S v b τ p k l ≤
      (axialCoefficient v b + 2 * kappa v b / (3 * v)) * ‖p‖ ^ 2 := by
  have hσlo : -1 ≤ S.sigma := by nlinarith [S.sigma_rho_circle, sq_nonneg S.rho]
  have hσhi : S.sigma ≤ 1 := by nlinarith [S.sigma_rho_circle, sq_nonneg S.rho]
  have ha := axial_reduction_vectors hv hb hsum hσlo hσhi
    (by nlinarith [S.sigma_rho_circle]) (-p) k l
  simp only [norm_neg, inner_neg_left] at ha
  have hE : 0 ≤ (parameters S p k l).squaredNorm / 6 := by
    rw [parameters_energy]
    positivity
  have ht : 0 ≤ (51 / 5 : ℝ) * (1 - τ) * b ^ 2 *
      ((parameters S p k l).squaredNorm / 6) := by
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (by norm_num) (sub_nonneg.mpr hτ)
      · exact sq_nonneg b
    · exact hE
  have hi := hessian_quadratic_axial_identity S v b τ p k l (ne_of_gt hv)
  linarith only [ha, ht, hi]

end
end PositiveEinsteinFour
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RealVectorProjection
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real-vector norm calculation behind the plus projection cost. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

/-- The real quaternion frame is orthogonal, with common norm `|a|`.
This includes the scalar direction and avoids any complex factorization. -/
theorem quaternion_combination_norm_sq (a : Vec) (r : ℝ) (c : Fin 3 → ℝ) :
    (∑ i : Fin 4, (r * a i + ∑ s : Fin 3, c s * quaternion s a i) ^ 2) =
      (r ^ 2 + ∑ s : Fin 3, c s ^ 2) * ‖a‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, quaternion, Fin.sum_univ_succ]
  ring

private theorem weightPlusPart_outer_norm (a : Vec) (Z : Tensor)
    (b c : Fin 3) (j : Fin 4) :
    (∑ i : Fin 4, weightPlusPart a Z i j b c ^ 2) =
      (‖a‖ ^ 2 / 144) * (49 * Z.matrix b c j ^ 2 +
        ∑ s : Fin 3, gradientGenerator s Z b c j ^ 2) := by
  have h := quaternion_combination_norm_sq a (7 * Z.matrix b c j)
    (fun s => -gradientGenerator s Z b c j)
  have hentry (i : Fin 4) :
      7 * a i * Z.matrix b c j -
          ∑ s : Fin 3, quaternion s a i * gradientGenerator s Z b c j =
        (7 * Z.matrix b c j) * a i +
          ∑ s : Fin 3, (-gradientGenerator s Z b c j) * quaternion s a i := by
    simp only [Fin.sum_univ_three]
    ring
  simp only [weightPlusPart, weightCoupling, hentry, div_pow, ← Finset.sum_div]
  rw [h]
  simp only [neg_sq, mul_pow]
  ring

/-- The coefficient `7/12` is proved directly for real vectors using the
actual Bianchi Casimir, with no representation or partial-trace premise. -/
theorem weightPlusPart_norm (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    hessianNormSq (weightPlusPart a Z) = (7 / 12) * ‖a‖ ^ 2 * Z.squaredNorm := by
  have hZ : (∑ b, ∑ c, ∑ j : Fin 4, Z.matrix b c j ^ 2) = Z.squaredNorm := by
    simp only [Tensor.squaredNorm, EuclideanSpace.real_norm_sq_eq]
  have hG : (∑ b, ∑ c, ∑ j : Fin 4, ∑ s : Fin 3,
      gradientGenerator s Z b c j ^ 2) = 35 * Z.squaredNorm := by
    calc
      _ = ∑ b, ∑ c, ∑ s : Fin 3, ∑ j : Fin 4,
          gradientGenerator s Z b c j ^ 2 := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_comm]
      _ = _ := by
        simpa only [EuclideanSpace.real_norm_sq_eq] using gradientGenerator_energy Z hz hb
  calc
    _ = ∑ b, ∑ c, ∑ j : Fin 4, ∑ i : Fin 4, weightPlusPart a Z i j b c ^ 2 := by
      unfold hessianNormSq
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ j : Fin 4,
        (‖a‖ ^ 2 / 144) * (49 * Z.matrix b c j ^ 2 +
          ∑ s : Fin 3, gradientGenerator s Z b c j ^ 2) := by
      simp_rw [weightPlusPart_outer_norm]
    _ = (‖a‖ ^ 2 / 144) *
        (49 * (∑ b, ∑ c, ∑ j : Fin 4, Z.matrix b c j ^ 2) +
          ∑ b, ∑ c, ∑ j : Fin 4, ∑ s : Fin 3, gradientGenerator s Z b c j ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hZ, hG]; ring

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RealVectorCost
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second real-vector projection identity in actual tensor coordinates. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian HighestHessian


theorem weightPlusPart_linearCombination (a : Vec) (Z : Tensor) :
    weightPlusPart a Z = (1 / 12 : ℝ) •
      ((7 : ℝ) • rawWeight a Z.matrix -
        ∑ r : Fin 3, rawWeight (quaternion r a) (rawGradientGenerator r Z.matrix)) := by
  funext i j b c
  simp [weightPlusPart, weightCoupling, rawWeight, Fin.sum_univ_three]
  ring

/-- This is the same explicit polynomial as the self-adjoint coupled operator. -/
theorem weightPlusPart_eq_plusPolynomial (a : Vec) (Z : Tensor) :
    weightPlusPart a Z = plusPolynomial (weightTensor a Z) := by
  rw [weightPlusPart_linearCombination]
  change _ = plusPolynomial (rawWeight a Z.matrix)
  rw [plusPolynomial, coupledOperator_rawWeight]

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
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

local instance metricRicciNormedRing_r6a8ae1_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricRicciNormedSpace_r6a8ae1_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricRicciNormedAlgebra_r6a8ae1_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem rawMatrixSlice_gradientTensor (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (j : Fin 4) :
    rawMatrixSlice (gradientTensor Z).matrix j = Z j := by
  ext a b
  simp only [rawMatrixSlice, gradientTensor_matrix Z hs]

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

local instance metricContractionNormedRing_r6a8ae1_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricContractionNormedSpace_r6a8ae1_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricContractionNormedAlgebra_r6a8ae1_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
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

private theorem orthogonal_matrix_contraction (P : Mat4) (hP : P * Pᵀ = 1)
    (f : Fin 4 → Fin 4 → Mat) :
    (∑ i, ∑ j, ∑ k, (P j i * P k i) • f j k) = ∑ j, f j j := by
  have hp (j k : Fin 4) : (∑ i, P j i * P k i) = if j = k then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun N : Mat4 => N j k) hP
  calc
    _ = ∑ j, ∑ i, ∑ k, (P j i * P k i) • f j k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, (P j i * P k i) • f j k := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ k, (if j = k then (1 : ℝ) else 0) • f j k := by
      simp only [← Finset.sum_smul, hp]
    _ = _ := by simp

theorem sum_squares_turnGradient (R : Mat) (hR : R * Rᵀ = 1)
    (P : Mat4) (hP : P * Pᵀ = 1) (Z : Angular.Gradient) :
    (∑ i, turnGradient R P Z i * turnGradient R P Z i) =
      conjugateMatrix R (∑ i, Z i * Z i) := by
  simp only [turnGradient, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, Finset.smul_sum, smul_smul, conjugateMatrix_mul R hR]
  change (∑ i, ∑ j, ∑ k, (P j i * P k i) • conjugateMatrix R (Z k * Z j)) = _
  rw [orthogonal_matrix_contraction P hP, conjugateMatrix_sum]

theorem weighted_sum_turnGradient (R : Mat) (P : Mat4) (hP : P * Pᵀ = 1)
    (a : Fin 4 → ℝ) (Z : Angular.Gradient) :
    (∑ i, (∑ k, P k i * a k) • turnGradient R P Z i) =
      conjugateMatrix R (∑ j, a j • Z j) := by
  change (∑ i, (∑ k, P k i * a k) •
    (∑ j, P j i • conjugateMatrix R (Z j))) = _
  calc
    _ = ∑ i, ∑ k, ∑ j, (P k i * a k) •
        (P j i • conjugateMatrix R (Z j)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_smul]
      simp only [Finset.smul_sum]
    _ = ∑ i, ∑ k, ∑ j, (P k i * P j i) • (a k • conjugateMatrix R (Z j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      simp only [smul_smul]
      congr 1
      ring
    _ = ∑ j, a j • conjugateMatrix R (Z j) := orthogonal_matrix_contraction P hP _
    _ = _ := by simp only [conjugateMatrix_sum, conjugateMatrix_smul]

theorem weightedCubicField_eq (a : Fin 4 → ℝ) (Z : Angular.Gradient) :
    weightedCubicField a Z =
      Matrix.trace ((∑ i, a i • Z i) * (∑ j, Z j * Z j)) := by
  simp only [weightedCubicField, Matrix.sum_mul, Matrix.smul_mul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]

/-- The full cubic trace, including its distinguished covector, is
preserved by the same local change of frame. -/
theorem weightedCubicField_turn (R : Mat) (hR : R * Rᵀ = 1)
    (P : Mat4) (hP : P * Pᵀ = 1) (a : Fin 4 → ℝ) (Z : Angular.Gradient) :
    weightedCubicField (fun i => ∑ k, P k i * a k) (turnGradient R P Z) =
      weightedCubicField a Z := by
  rw [weightedCubicField_eq, weighted_sum_turnGradient R P hP,
    sum_squares_turnGradient R hR P hP, conjugateMatrix_mul R hR,
    conjugateMatrix_trace R hR, weightedCubicField_eq]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The actual spectral minimum is itself an admissible curvature shift.
This permits the coefficient `y=b*s`, rather than an arbitrary
larger positive-semidefinite shift. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem conjugateMatrix_inverse (R : Mat) (hR : R * Rᵀ = 1) (A : Mat) :
    conjugateMatrix Rᵀ (conjugateMatrix R A) = A := by
  unfold conjugateMatrix
  rw [Matrix.transpose_transpose]
  calc
    R * (Rᵀ * A * R) * Rᵀ = (R * Rᵀ) * A * (R * Rᵀ) := by
      simp only [Matrix.mul_assoc]
    _ = A := by rw [hR, Matrix.one_mul, Matrix.mul_one]

/-- The lower bound on every normalized eigenvalue gives positive
semidefiniteness at the exact minimum shift. -/
theorem shape_minimum_shift_posSemidef (A R : Mat) (hR : Rᵀ * R = 1)
    (S : Shape) (v r : ℝ) (hv : 0 ≤ v)
    (hdiag : conjugateMatrix R A = Matrix.diagonal (fun i => v * S.s i))
    (hmin : ∀ i, -r ≤ S.s i) :
    (A + (v * r) • (1 : Mat)).PosSemidef := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  have hnon (i : Fin 3) : 0 ≤ v * S.s i + v * r := by
    have hp := mul_nonneg hv (show 0 ≤ S.s i + r by linarith only [hmin i])
    nlinarith only [hp]
  have hsum : Matrix.diagonal (fun i => v * S.s i + v * r) =
      Matrix.diagonal (fun i => v * S.s i) + (v * r) • (1 : Mat) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.add_apply, Matrix.smul_apply, hij]
  have hp : (conjugateMatrix R (A + (v * r) • (1 : Mat))).PosSemidef := by
    rw [conjugateMatrix_add, conjugateMatrix_smul, conjugateMatrix_one R hR, hdiag, ← hsum]
    exact Matrix.posSemidef_diagonal_iff.mpr hnon
  have hb := conjugateMatrix_posSemidef Rᵀ _ hp
  rw [conjugateMatrix_inverse R hR'] at hb
  exact hb

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The sharp cubic estimate in an arbitrary frame. The diagonalized
matrix is the contraction of the gradient with its distinguished covector,
not the Weyl matrix and not a moving eigenframe. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem weightedCubicField_tensor (a : Vec) (Z : Angular.Gradient)
    (hZ : ∀ i, symmetric (Z i)) :
    weightedCubicField a Z = weightedCubicTrace a (gradientTensor Z) := by
  have hd (i : Fin 4) : derivativeMatrix (gradientTensor Z) i = Z i := by
    ext r s
    exact congrArg (fun v : Vec => v i) (gradientTensor_matrix Z hZ r s)
  simp only [weightedCubicField, weightedCubicTrace, hd]

theorem weightedCubicField_smul (c : ℝ) (a : Vec) (Z : Angular.Gradient) :
    weightedCubicField (c • a) Z = c * weightedCubicField a Z := by
  simp only [weightedCubicField, Pi.smul_apply, smul_eq_mul, mul_assoc,
    Finset.mul_sum]

private theorem distinguished_matrix_symmetric (a : Vec) (Z : Angular.Gradient)
    (hZ : ∀ i, symmetric (Z i)) : symmetric (∑ i, a i • Z i) := by
  intro r s
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hZ i r s]

private theorem distinguished_matrix_traceFree (a : Vec) (Z : Angular.Gradient)
    (hZ : ∀ i, traceFree (Z i)) : traceFree (∑ i, a i • Z i) := by
  change Matrix.trace (∑ i, a i • Z i) = 0
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_smul, show ∀ i, Matrix.trace (Z i) = 0 from hZ,
    smul_zero, Finset.sum_const_zero]

private theorem distinguished_matrix_turn (R : Mat) (P : Mat4)
    (hP : P * Pᵀ = 1) (a : Vec) (Z : Angular.Gradient) :
    (∑ i, (turnVector P a) i • turnGradient R P Z i) =
      conjugateMatrix R (∑ i, a i • Z i) := by
  simpa only [turnVector, Matrix.mulVec, Matrix.transpose_apply, dotProduct] using
    weighted_sum_turnGradient R P hP a Z

/-- Sharp cubic contraction for arbitrary symmetric trace-free Bianchi
gradients and arbitrary distinguished covectors. -/
theorem weightedCubicField_sharp (a : Vec) (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0) :
    |weightedCubicField a Z| ≤ ‖a‖ *
      ((24 / 5 : ℝ) * Real.sqrt (3 / 5) * weylGradientEnergy Z *
        Real.sqrt (weylGradientEnergy Z)) := by
  have he : 0 ≤ weylGradientEnergy Z := by
    unfold weylGradientEnergy matrixPairing
    apply div_nonneg _ (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro r _
    apply Finset.sum_nonneg
    intro s _
    exact mul_self_nonneg _
  by_cases ha : a = 0
  · simp [ha, weightedCubicField]
  let a₀ : Vec := (‖a‖⁻¹ : ℝ) • a
  have ha₀ : ‖a₀‖ = 1 := norm_smul_inv_norm ha
  have harec : a = ‖a‖ • a₀ := by
    dsimp only [a₀]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha), one_smul]
  suffices hunit : |weightedCubicField a₀ Z| ≤
      (24 / 5 : ℝ) * Real.sqrt (3 / 5) * weylGradientEnergy Z *
        Real.sqrt (weylGradientEnergy Z) by
    have hhom : weightedCubicField a Z = ‖a‖ * weightedCubicField a₀ Z := by
      conv_lhs => rw [harec]
      exact weightedCubicField_smul ‖a‖ a₀ Z
    rw [hhom, abs_mul, abs_of_nonneg (norm_nonneg a)]
    exact mul_le_mul_of_nonneg_left hunit (norm_nonneg a)
  let M : Mat := ∑ i, a₀ i • Z i
  by_cases hM : M = 0
  · have hc : weightedCubicField a₀ Z = 0 := by
      rw [weightedCubicField_eq]
      change Matrix.trace (M * _) = 0
      rw [hM, Matrix.zero_mul, Matrix.trace_zero]
    rw [hc, abs_zero]
    positivity
  have hMv : 0 < normalizedBlockNorm M :=
    lt_of_le_of_ne (normalizedBlockNorm_nonneg M)
      (Ne.symm (mt (normalizedBlockNorm_eq_zero_iff M).mp hM))
  obtain ⟨R, hR, ⟨P⟩, S, hdiag⟩ := exists_lifted_spectral_shape M
    (distinguished_matrix_symmetric a₀ Z hs) (distinguished_matrix_traceFree a₀ Z ht) hMv
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  let Z' := turnGradient R P.matrix Z
  let a' := turnVector P.matrix a₀
  have hs' : ∀ i, symmetric (Z' i) := turnGradient_symmetric R P.matrix Z hs
  have ht' : ∀ i, traceFree (Z' i) := turnGradient_traceFree R hR' P.matrix Z ht
  have hb' : ∀ r i, gradientDivergence Z' r i = 0 := turnGradient_bianchi R hR' P Z hb
  have ha' : ‖a'‖ = 1 := (turnVector_norm P.matrix P.mul_transpose a₀).trans ha₀
  have hshape (r s : Fin 3) :
      inner ℝ a' ((gradientTensor Z').matrix r s) =
        if r = s then normalizedBlockNorm M * S.s r else 0 := by
    rw [gradientTensor_matrix Z' hs']
    have h := congrArg (fun N : Mat => N r s)
      ((distinguished_matrix_turn R P.matrix P.mul_transpose a₀ Z).trans hdiag)
    simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul,
      mul_comm, a', Z', M, conjugateMatrix] using h
  have hc := cubicContraction_sharp_tensor_diagonal S a' (gradientTensor Z')
    (gradientTensor_traceFree Z' ht') (gradientTensor_bianchi Z' hs' hb') ha'
    (normalizedBlockNorm_nonneg M) hshape
  have he' : (gradientTensor Z').squaredNorm / 6 = weylGradientEnergy Z := by
    rw [gradientTensor_energy Z' hs', weylGradientEnergy_turn R hR' P.matrix P.mul_transpose]
  rw [he'] at hc
  have hcube : weightedCubicField a' Z' = weightedCubicField a₀ Z := by
    change weightedCubicField (fun i => ∑ k, P.matrix k i * a₀ k)
      (turnGradient R P.matrix Z) = weightedCubicField a₀ Z
    exact weightedCubicField_turn R hR' P.matrix P.mul_transpose a₀ Z
  rw [← hcube, weightedCubicField_tensor a' Z' hs', weightedCubicTrace_eq, abs_mul]
  norm_num only [abs_of_pos (show (0 : ℝ) < 6 by norm_num)]
  nlinarith only [hc]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The sharp opposite-block cost for an arbitrary symmetric coefficient
matrix.  A concrete orthogonal quaternion expansion of the two derivative
slots replaces a second choice of eigenframe. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- The exact Parseval identity for this real orthogonal expansion. -/
theorem rightQuaternionCoefficients_pairing (M N : Mat4) :
    (∑ a, ∑ b, rightQuaternionCoefficients M a b * rightQuaternionCoefficients N a b) =
      ∑ i, ∑ j, M i j * N i j := by
  norm_num [rightQuaternionCoefficients, Fin.sum_univ_four]
  ring

private theorem rightQuaternionCoefficients_action_zero (M : Mat4) :
    rightQuaternionCoefficients (rightMatrixAction 0 M) =
      rightCoefficientAction 0 (rightQuaternionCoefficients M) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rightQuaternionCoefficients, rightMatrixAction, rightCoefficientAction,
      rightQuaternion, Fin.sum_univ_four] <;> ring

private theorem rightQuaternionCoefficients_action_one (M : Mat4) :
    rightQuaternionCoefficients (rightMatrixAction 1 M) =
      rightCoefficientAction 1 (rightQuaternionCoefficients M) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rightQuaternionCoefficients, rightMatrixAction, rightCoefficientAction,
      rightQuaternion, Fin.sum_univ_four] <;> ring

private theorem rightQuaternionCoefficients_action_two (M : Mat4) :
    rightQuaternionCoefficients (rightMatrixAction 2 M) =
      rightCoefficientAction 2 (rightQuaternionCoefficients M) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rightQuaternionCoefficients, rightMatrixAction, rightCoefficientAction,
      rightQuaternion, Fin.sum_univ_four] <;> ring

private theorem rightQuaternionCoefficients_action (r : Fin 3) (M : Mat4) :
    rightQuaternionCoefficients (rightMatrixAction r M) =
      rightCoefficientAction r (rightQuaternionCoefficients M) := by
  fin_cases r
  · exact rightQuaternionCoefficients_action_zero M
  · exact rightQuaternionCoefficients_action_one M
  · exact rightQuaternionCoefficients_action_two M

private theorem rightCoefficientAction_pairing (r s : Fin 3) (C : Mat4) :
    (∑ a, ∑ b, rightCoefficientAction r C a b * rightCoefficientAction s C a b) =
      4 * ((if r = s then ∑ a, ∑ t : Fin 3, C a t.succ ^ 2 else 0) -
        ∑ a, C a r.succ * C a s.succ) := by
  fin_cases r <;> fin_cases s <;>
    simp [rightCoefficientAction, Fin.sum_univ_four, Fin.sum_univ_three] <;> ring

private theorem rightMatrixAction_pairing (r s : Fin 3) (M : Mat4) :
    (∑ i, ∑ j, rightMatrixAction r M i j * rightMatrixAction s M i j) =
      4 * ((if r = s then
          ∑ a, ∑ t : Fin 3, rightQuaternionCoefficients M a t.succ ^ 2 else 0) -
        ∑ a, rightQuaternionCoefficients M a r.succ *
          rightQuaternionCoefficients M a s.succ) := by
  rw [← rightQuaternionCoefficients_pairing,
    rightQuaternionCoefficients_action, rightQuaternionCoefficients_action]
  exact rightCoefficientAction_pairing r s (rightQuaternionCoefficients M)

/-- The omitted scalar right-quaternion coefficient has nonnegative energy. -/
theorem rightVectorEnergy_le (X : Hessian) : rightVectorEnergy X ≤ hessianNormSq X := by
  have h (a b : Fin 3) :
      (∑ t : Fin 4, ∑ r : Fin 3,
        rightQuaternionCoefficients (fun i j => X i j a b) t r.succ ^ 2) ≤
        ∑ i, ∑ j, X i j a b ^ 2 := by
    have hp := rightQuaternionCoefficients_pairing
      (fun i j => X i j a b) (fun i j => X i j a b)
    simp only [← pow_two] at hp
    rw [← hp]
    apply Finset.sum_le_sum
    intro t _
    simp only [Fin.sum_univ_four, Fin.sum_univ_three,
      show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
      show (1 : Fin 3).succ = (2 : Fin 4) from rfl,
      show (2 : Fin 3).succ = (3 : Fin 4) from rfl]
    linarith [sq_nonneg (rightQuaternionCoefficients (fun i j => X i j a b) t 0)]
  exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => h a b

private theorem sum_pair_triple (F : Fin 3 → Fin 3 → Fin 4 → Fin 3 → Fin 3 → ℝ) :
    (∑ r, ∑ s, ∑ a, ∑ b, ∑ t, F a b t r s) =
      ∑ a, ∑ b, ∑ t, ∑ r, ∑ s, F a b t r s := by
  have move (G : Fin 3 → Fin 3 → Fin 4 → Fin 3 → ℝ) :
      (∑ r, ∑ a, ∑ b, ∑ t, G a b t r) =
        ∑ a, ∑ b, ∑ t, ∑ r, G a b t r := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
  calc
    _ = ∑ r, ∑ a, ∑ b, ∑ t, ∑ s, F a b t r s := by
      apply Finset.sum_congr rfl
      intro r _
      exact move (fun a b t s => F a b t r s)
    _ = _ := move (fun a b t r => ∑ s, F a b t r s)

private theorem weighted_complement_gram (U H : Mat) (e : ℝ) :
    (∑ r, ∑ s, U r s * (4 * ((if r = s then e else 0) - H r s))) =
      4 * ((∑ r, U r r) * e - ∑ r, ∑ s, U r s * H r s) := by
  simp only [Fin.sum_univ_three]
  norm_num
  ring

/-- The complete minus Gram matrix is the scalar part minus this positive
three-dimensional Gram form. This identity is valid for every Hessian. -/
theorem hessianGram_totalMinus (U : Mat) (X : Hessian) :
    hessianGram U (fun r => totalMinus r X) =
      4 * ((∑ r, U r r) * rightVectorEnergy X - rightVectorGram U X) := by
  have hp (r s : Fin 3) :
      hessianPairing (totalMinus r X) (totalMinus s X) =
        4 * ((if r = s then rightVectorEnergy X else 0) -
          ∑ a, ∑ b, ∑ t : Fin 4,
            rightQuaternionCoefficients (fun i j => X i j a b) t r.succ *
              rightQuaternionCoefficients (fun i j => X i j a b) t s.succ) := by
    change (∑ a : Fin 3, ∑ b : Fin 3,
      ∑ i : Fin 4, ∑ j : Fin 4,
        rightMatrixAction r (fun i j => X i j a b) i j *
          rightMatrixAction s (fun i j => X i j a b) i j) = _
    have he (a b : Fin 3) := rightMatrixAction_pairing r s
      (show Mat4 from fun i j => X i j a b)
    simp_rw [he]
    by_cases hrs : r = s <;>
      simp [hrs, rightVectorEnergy, Finset.sum_sub_distrib, ← Finset.mul_sum]
  let H : Mat := fun r s => ∑ a : Fin 3, ∑ b : Fin 3, ∑ t : Fin 4,
    rightQuaternionCoefficients (fun i j => X i j a b) t r.succ *
      rightQuaternionCoefficients (fun i j => X i j a b) t s.succ
  have he : hessianGram U (fun r => totalMinus r X) =
      ∑ r : Fin 3, ∑ s : Fin 3,
        U r s * (4 * ((if r = s then rightVectorEnergy X else 0) - H r s)) := by
    unfold hessianGram
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    exact congrArg (fun z : ℝ => U r s * z) (hp r s)
  rw [he, weighted_complement_gram U H (rightVectorEnergy X)]
  congr 2
  dsimp only [H]
  simp only [Finset.mul_sum]
  rw [sum_pair_triple]
  unfold rightVectorGram
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Positive semidefiniteness is used only on the actual coefficient vectors. -/
theorem rightVectorGram_nonneg (U : Mat) (hU : U.PosSemidef) (X : Hessian) :
    0 ≤ rightVectorGram U X := by
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  apply Finset.sum_nonneg
  intro t _
  have h := hU.dotProduct_mulVec_nonneg
    (fun r => rightQuaternionCoefficients (fun i j => X i j a b) t r.succ)
  simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem rightVectorGram_shift (U : Mat) (y : ℝ) (X : Hessian) :
    rightVectorGram (U + y • (1 : Mat)) X =
      rightVectorGram U X + y * rightVectorEnergy X := by
  have h (c : Fin 3 → ℝ) :
      (∑ r, ∑ s, (U + y • (1 : Mat)) r s * c r * c s) =
        (∑ r, ∑ s, U r s * c r * c s) + y * ∑ r, c r ^ 2 := by
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Fin.sum_univ_three]
    norm_num
    ring
  unfold rightVectorGram rightVectorEnergy
  simp_rw [h]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Sharp opposite-block upper cost, with no eigenframe and no additional
condition on the two-derivative tensor. -/
theorem general_minus_cost (U : Mat) (hU : traceFree U) (y : ℝ) (hy : 0 ≤ y)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (X : Hessian) :
    hessianGram U (fun r => totalMinus r X) / 4 ≤ y * hessianNormSq X := by
  have h := rightVectorGram_nonneg _ hUy X
  rw [rightVectorGram_shift] at h
  rw [hessianGram_totalMinus, hU]
  have he := mul_le_mul_of_nonneg_left (rightVectorEnergy_le X) hy
  nlinarith only [h, he]

/-- The sign of the shift is already forced by the matrix hypotheses. -/
theorem general_minus_cost_of_shift (U : Mat) (hU : traceFree U) (y : ℝ)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (X : Hessian) :
    hessianGram U (fun r => totalMinus r X) / 4 ≤ y * hessianNormSq X :=
  general_minus_cost U hU y (shift_nonneg_of_traceFree U hU y hUy) hUy X

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The sharp real-vector projection cost in an arbitrary Weyl frame. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

/-- The original sharp projection bound, with no diagonal frame assumption. -/
theorem general_highestProjection_weight_cost (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (a : Vec) (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    generalCurvaturePairing A U
      (highestProjection (weightTensor a Z)) (highestProjection (weightTensor a Z)) ≤
      ‖a‖ ^ 2 * ((7 / 12 : ℝ) * (4 + y) * Z.squaredNorm -
        (5 / 4 : ℝ) * generalGradientForm A Z) := by
  have hproj : highestProjection (weightPlusPart a Z) =
      highestProjection (weightTensor a Z) := by
    rw [weightPlusPart_eq_plusPolynomial, highestProjection_plusPolynomial]
  have hp := general_highestProjection_curvature_le A U hA hU x y
    (shift_nonneg_of_traceFree U htU y hUy) hAx hUy hxy (weightPlusPart a Z)
    (weightPlusPart_plus_energy a Z hz hb)
  rw [hproj] at hp
  have hm := general_minus_cost_of_shift U htU y hUy (weightPlusPart a Z)
  have hc := totalPlus_weightPlusPart_generalCost A hA htA a Z hz hb
  have hn := weightPlusPart_norm a Z hz hb
  conv_rhs at hp =>
    rw [generalCurvaturePairing_self]
    unfold generalCasimirCurvatureForm
  rw [hc, hn] at hp
  rw [hn] at hm
  nlinarith only [hp, hm]

end
end PositiveEinsteinFour.HighestHessian
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

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The actual highest-Hessian projection cost in invariant energy units,
then in the same spectral parameters as the Hessian estimate. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian HighestHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

/-- Normalize the arbitrary-frame real-vector cost without rotating the
opposite block or the weight covector. -/
theorem invariant_projection_cost (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (a : Vec) (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0) :
    generalCurvaturePairing A U
        (highestProjection (weightTensor a (gradientTensor Z)))
        (highestProjection (weightTensor a (gradientTensor Z))) / 6 ≤
      ‖a‖ ^ 2 * ((7 / 12 : ℝ) * (4 + y) * weylGradientEnergy Z -
        (5 / 4 : ℝ) * weylMatrixEnergy A Z) := by
  have hc := general_highestProjection_weight_cost A U hA hU htA htU x y hAx hUy hxy
    a (gradientTensor Z) (gradientTensor_traceFree Z ht) (gradientTensor_bianchi Z hs hb)
  have hg : generalGradientForm A (gradientTensor Z) = 6 * weylMatrixEnergy A Z :=
    generalMatrixAction_gradient_pairing A Z hs
  have he : (gradientTensor Z).squaredNorm = 6 * weylGradientEnergy Z := by
    have he' := gradientTensor_energy Z hs
    linarith only [he']
  have hd := div_le_div_of_nonneg_right hc (show (0 : ℝ) ≤ 6 by norm_num)
  rw [hg, he] at hd
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  ring

/-- The normalized invariant cost is bounded by the source's exact two
spectral coefficients, retaining the actual total derivative energy. -/
theorem invariant_projection_parameter_cost (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (a : Vec) (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0)
    (S : Shape) (p k l : Vec)
    (he : (parameters S p k l).squaredNorm / 6 = weylGradientEnergy Z)
    (hB : weylMatrixEnergy A Z =
      curvatureContraction S (normalizedBlockNorm A) (parameters S p k l)) :
    generalCurvaturePairing A U
        (highestProjection (weightTensor a (gradientTensor Z)))
        (highestProjection (weightTensor a (gradientTensor Z))) / 6 ≤
      ‖a‖ ^ 2 *
        (QuarticEnergy.projectionCoefficient (normalizedBlockNorm A) y S.sigma S.rho *
          ((5 / 3) * ‖p‖ ^ 2) + Energy.defectCoefficient (normalizedBlockNorm A) y *
          (weylGradientEnergy Z - (5 / 3) * ‖p‖ ^ 2)) := by
  have hc := invariant_projection_cost A U hA hU htA htU x y hAx hUy hxy a Z hs ht hb
  have hp := projection_cost_coefficients S (normalizedBlockNorm_nonneg A) y p k l
  rw [he, ← hB] at hp
  exact hc.trans (mul_le_mul_of_nonneg_left hp (sq_nonneg ‖a‖))

end
end PositiveEinsteinFour.QuaternionFrame
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Identify the scalar terms in the metric norm and trace-energy
equations in a single pointwise spectral frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi QuaternionFrame Matrix
open scoped BigOperators

noncomputable section

theorem shape_fourth_moment (S : Shape) : (∑ i, S.s i ^ 4) = 18 := by
  have ht := S.trace
  simp only [Fin.sum_univ_three] at ht
  have hz : S.s 2 = -S.s 0 - S.s 1 := by linarith
  calc
    _ = (∑ i, S.s i ^ 2) ^ 2 / 2 := by
      simp only [Fin.sum_univ_three]
      rw [hz]
      ring
    _ = 18 := by rw [S.square]; norm_num

theorem weylLaplacian_shape (S : Shape) (v : ℝ) :
    weylLaplacian (Matrix.diagonal (fun i => v * S.s i)) =
      Matrix.diagonal (fun i => 6 * (v * S.s i - v ^ 2 * (S.s i ^ 2 - 2))) := by
  unfold weylLaplacian
  rw [shape_traceFreeSquare]
  ext a b
  by_cases hab : a = b
  · subst b
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply_eq,
      smul_eq_mul, Shape.squareWeight]
  · simp [Matrix.smul_apply, Matrix.diagonal_apply_ne _ hab]

theorem matrixNormSq_diagonal (t : Fin 3 → ℝ) :
    matrixNormSq (Matrix.diagonal t) = ∑ i, t i ^ 2 := by
  simp [matrixNormSq, Matrix.diagonal_apply]

theorem traceEnergy_shape (S : Shape) (v : ℝ) :
    traceEnergy (Matrix.diagonal (fun i => v * S.s i)) =
      30 * v ^ 2 * (1 - 2 * S.sigma * v + v ^ 2) := by
  have h3 : (∑ i, S.s i ^ 3) = 6 * S.sigma := by
    unfold Shape.sigma
    ring
  have hp (i : Fin 3) : (6 * (v * S.s i - v ^ 2 * (S.s i ^ 2 - 2))) ^ 2 =
      (36 * v ^ 2) * S.s i ^ 2 - (72 * v ^ 3) * S.s i ^ 3 +
      (144 * v ^ 3) * S.s i + (36 * v ^ 4) * S.s i ^ 4 -
      (144 * v ^ 4) * S.s i ^ 2 + 144 * v ^ 4 := by ring
  unfold traceEnergy
  rw [weylLaplacian_shape, matrixNormSq_diagonal]
  simp only [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    S.square, S.trace, h3, shape_fourth_moment, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem weylLaplacian_conjugate (R A : Mat) (hR : Rᵀ * R = 1) :
    weylLaplacian (conjugateMatrix R A) = conjugateMatrix R (weylLaplacian A) := by
  simp only [weylLaplacian, conjugateMatrix_traceFreeSquare R hR,
    conjugateMatrix_smul, conjugateMatrix_sub]

theorem traceEnergy_conjugate (R A : Mat) (hR : Rᵀ * R = 1) :
    traceEnergy (conjugateMatrix R A) = traceEnergy A := by
  unfold traceEnergy
  rw [weylLaplacian_conjugate R A hR]
  have hp := conjugateMatrix_pairing R (mul_eq_one_comm.mp hR) (weylLaplacian A) (weylLaplacian A)
  have hn : matrixNormSq (conjugateMatrix R (weylLaplacian A)) = matrixNormSq (weylLaplacian A) := by
    simpa only [matrixNormSq, matrixPairing, pow_two] using hp
  rw [hn]

theorem traceEnergy_spectral (A R : Mat) (hR : Rᵀ * R = 1) (S : Shape) (v : ℝ)
    (hdiag : conjugateMatrix R A = Matrix.diagonal (fun i => v * S.s i)) :
    traceEnergy A = 30 * v ^ 2 * (1 - 2 * S.sigma * v + v ^ 2) := by
  rw [← traceEnergy_conjugate R A hR, hdiag, traceEnergy_shape]

theorem trace_mul_weylLaplacian_shape (S : Shape) (v : ℝ) :
    Matrix.trace (Matrix.diagonal (fun i => v * S.s i) *
      weylLaplacian (Matrix.diagonal (fun i => v * S.s i))) =
      36 * v ^ 2 * (1 - S.sigma * v) := by
  rw [weylLaplacian_shape, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  have hp (i : Fin 3) : v * S.s i * (6 * (v * S.s i - v ^ 2 * (S.s i ^ 2 - 2))) =
      (6 * v ^ 2) * S.s i ^ 2 - (6 * v ^ 3) * S.s i ^ 3 + (12 * v ^ 3) * S.s i := by ring
  have h3 : (∑ i, S.s i ^ 3) = 6 * S.sigma := by unfold Shape.sigma; ring
  simp only [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    S.square, S.trace, h3]
  ring

theorem radialLaplacian_spectral (A R : Mat) (hR : Rᵀ * R = 1) (S : Shape)
    (hv : 0 < normalizedBlockNorm A)
    (hdiag : conjugateMatrix R A = Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i)) :
    regularizedRadialDerivative 0 A (weylLaplacian A) =
      6 * normalizedBlockNorm A * (1 - S.sigma * normalizedBlockNorm A) := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  have ht : Matrix.trace (A * weylLaplacian A) =
      36 * normalizedBlockNorm A ^ 2 * (1 - S.sigma * normalizedBlockNorm A) := by
    calc
      _ = Matrix.trace (conjugateMatrix R (A * weylLaplacian A)) :=
        (conjugateMatrix_trace R hR' _).symm
      _ = Matrix.trace (conjugateMatrix R A * weylLaplacian (conjugateMatrix R A)) := by
        rw [weylLaplacian_conjugate R A hR, conjugateMatrix_mul R hR']
      _ = _ := by rw [hdiag, trace_mul_weylLaplacian_shape]
  unfold regularizedRadialDerivative
  rw [regularizedBlockNorm_zero, ht]
  field_simp [ne_of_gt hv]
  ring

theorem scalarNormExpression_spectral (A R : Mat) (hR : Rᵀ * R = 1)
    (S : Shape) (Z : Angular.Gradient) (hv : 0 < normalizedBlockNorm A)
    (hdiag : conjugateMatrix R A = Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i)) :
    scalarNormExpression 0 A Z =
      (weylGradientEnergy Z - ‖blockRadialGradient A Z‖ ^ 2) / normalizedBlockNorm A +
        6 * normalizedBlockNorm A * (1 - S.sigma * normalizedBlockNorm A) := by
  unfold scalarNormExpression
  rw [regularizedBlockNorm_zero, radialLaplacian_spectral A R hR S hv hdiag,
    EuclideanSpace.real_norm_sq_eq]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Norm-only forms of the cubic and true projection estimates. These are
unchanged by reflecting the opposite block's covector coordinates. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian HighestHessian PositiveEinsteinFour.Geometry CurvatureContraction
open Energy QuarticEnergy Quadratic Potential

noncomputable section

theorem projectionBracket_nonneg {v y σ ρ e radial : ℝ}
    (hv : 0 ≤ v) (hv2 : v ≤ 2) (hy : 0 ≤ y) (hσ : σ ≤ 1)
    (hrad : 0 ≤ radial) (he : (5 / 3) * radial ≤ e) :
    0 ≤ projectionBracket v y σ ρ e radial := by
  have hσv := mul_le_mul_of_nonneg_right hσ hv
  have hρ : 0 ≤ ρ ^ 2 * v ^ 2 / 4 := by positivity
  have hg : 0 ≤ projectionCoefficient v y σ ρ := by
    unfold projectionCoefficient
    nlinarith only [hσv, hρ, hy, hv2]
  have hH : 0 ≤ defectCoefficient v y := by
    unfold defectCoefficient
    positivity
  unfold projectionBracket
  exact add_nonneg (mul_nonneg hg (by positivity)) (mul_nonneg hH (sub_nonneg.mpr he))

theorem norm_of_weight_square (M : ℝ) (hM : 0 ≤ M) (a p q : Vec)
    (ha : ‖a‖ ^ 2 = (9 / 16 : ℝ) * M ^ 2 * ‖p - q‖ ^ 2) :
    ‖a‖ = (3 / 4 : ℝ) * M * ‖p - q‖ := by
  have hr : 0 ≤ (3 / 4 : ℝ) * M * ‖p - q‖ := by positivity
  have hs : ((3 / 4 : ℝ) * M * ‖p - q‖) ^ 2 = ‖a‖ ^ 2 := by
    rw [ha]
    ring
  nlinarith only [hs, hr, norm_nonneg a]

/-- Only the norm of the weight covector matters, so this also applies
to the reflected opposite block. -/
theorem cubic_bound_of_weight_square (M : ℝ) (hM : 0 ≤ M) (a p q : Vec)
    (ha : ‖a‖ ^ 2 = (9 / 16 : ℝ) * M ^ 2 * ‖p - q‖ ^ 2)
    (Z : Angular.Gradient) (hs : ∀ i, symmetric (Z i))
    (ht : ∀ i, traceFree (Z i)) (hb : ∀ r i, gradientDivergence Z r i = 0) :
    -(5 / 36 : ℝ) * weightedCubicField a Z ≤
      (1 / 2 : ℝ) * Real.sqrt (3 / 5) * (‖p‖ + ‖q‖) * M *
        (weylGradientEnergy Z * Real.sqrt (weylGradientEnergy Z)) := by
  have he : 0 ≤ weylGradientEnergy Z := by
    unfold weylGradientEnergy matrixPairing
    apply div_nonneg _ (by norm_num)
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => mul_self_nonneg (Z i j k)
  have hn : ‖a‖ ≤ (3 / 4 : ℝ) * M * (‖p‖ + ‖q‖) := by
    rw [norm_of_weight_square M hM a p q ha]
    exact mul_le_mul_of_nonneg_left (norm_sub_le p q) (by positivity)
  have hc := weightedCubicField_sharp a Z hs ht hb
  have hu := hc.trans (mul_le_mul_of_nonneg_right hn
    (show 0 ≤ (24 / 5 : ℝ) * Real.sqrt (3 / 5) * weylGradientEnergy Z *
      Real.sqrt (weylGradientEnergy Z) by positivity))
  have hlo := (abs_le.mp hu).1
  nlinarith only [hlo]

/-- The true projected cost, with a norm-specified weight derivative. -/
theorem projection_bound_of_weight_square (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (M : ℝ) (hM : M ≠ 0) (a p q : Vec)
    (ha : ‖a‖ ^ 2 = (9 / 16 : ℝ) * M ^ 2 * ‖p - q‖ ^ 2)
    (Z : Angular.Gradient) (hs : ∀ i, symmetric (Z i))
    (ht : ∀ i, traceFree (Z i)) (hb : ∀ r i, gradientDivergence Z r i = 0)
    (S : Shape) (p' k l : Vec)
    (he : (parameters S p' k l).squaredNorm / 6 = weylGradientEnergy Z)
    (hp : ‖p'‖ ^ 2 = ‖p‖ ^ 2)
    (hB : weylMatrixEnergy A Z =
      curvatureContraction S (normalizedBlockNorm A) (parameters S p' k l)) :
    generalCurvaturePairing A U
        (highestProjection (weightTensor a (gradientTensor Z)))
        (highestProjection (weightTensor a (gradientTensor Z))) / (24 * M ^ 2) ≤
      (9 / 64 : ℝ) * ‖p - q‖ ^ 2 *
        projectionBracket (normalizedBlockNorm A) y S.sigma S.rho
          (weylGradientEnergy Z) (‖p‖ ^ 2) := by
  have hc := invariant_projection_parameter_cost A U hA hU htA htU x y hAx hUy hxy
    a Z hs ht hb S p' k l he hB
  rw [hp] at hc
  have hd := div_le_div_of_nonneg_right hc (show 0 ≤ 4 * M ^ 2 by positivity)
  rw [ha] at hd
  unfold projectionBracket
  convert hd using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp [hM] <;> ring)

theorem projection_bound_norm_sum {v y σ ρ e : ℝ} (p q : Vec)
    (hv : 0 ≤ v) (hv2 : v ≤ 2) (hy : 0 ≤ y) (hσ : σ ≤ 1)
    (he : (5 / 3) * ‖p‖ ^ 2 ≤ e) :
    (9 / 64 : ℝ) * ‖p - q‖ ^ 2 * projectionBracket v y σ ρ e (‖p‖ ^ 2) ≤
      (9 / 64 : ℝ) * (‖p‖ + ‖q‖) ^ 2 * projectionBracket v y σ ρ e (‖p‖ ^ 2) := by
  have hn := norm_sub_le p q
  have hn0 := norm_nonneg (p - q)
  have hs : ‖p - q‖ ^ 2 ≤ (‖p‖ + ‖q‖) ^ 2 := by nlinarith only [hn, hn0]
  have hc := projectionBracket_nonneg (ρ := ρ) hv hv2 hy hσ (sq_nonneg ‖p‖) he
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (by norm_num)) hc

theorem gradientSum_radial (p q : Vec) :
    gradientSum ((5 / 3 : ℝ) * ‖p‖ ^ 2) ((5 / 3 : ℝ) * ‖q‖ ^ 2) = ‖p‖ + ‖q‖ := by
  have hp : Real.sqrt ((5 / 3 : ℝ) * ‖p‖ ^ 2) = Real.sqrt (5 / 3) * ‖p‖ := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg p)]
  have hq : Real.sqrt ((5 / 3 : ℝ) * ‖q‖ ^ 2) = Real.sqrt (5 / 3) * ‖q‖ := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg q)]
  have hroot : Real.sqrt (3 / 5 : ℝ) * Real.sqrt (5 / 3) = 1 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  unfold gradientSum
  rw [hp, hq, mul_add, ← mul_assoc, ← mul_assoc, hroot]
  ring

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Exact scalar separation into quartic, axial quadratic, and potential
terms. No geometric estimate is an assumption in these identities. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry
open Energy QuarticEnergy Quadratic Potential Boundary

noncomputable section

theorem scalar_potential_identity (v b σ τ : ℝ) :
    -(17 / 10 : ℝ) * (2 - v - b) *
        (30 * v ^ 2 * (1 - 2 * σ * v + v ^ 2) +
          30 * b ^ 2 * (1 - 2 * τ * b + b ^ 2)) +
      kappa v b * (6 * v * (1 - σ * v)) +
      kappa b v * (6 * b * (1 - τ * b)) -
      158 * (1 - (2 - v - b) ^ 2 / 4) * (v - b) ^ 2 =
    zeroOrderIntegrand v b σ τ := by
  unfold zeroOrderIntegrand zeroOrder spectralCoefficient
  ring

theorem scalarCouplingTerm_spectral_split (v b σ τ e f B C : ℝ) (p q : Vec) :
    scalarCouplingTerm v b e f B C
        ((e - ‖p‖ ^ 2) / v + 6 * v * (1 - σ * v))
        ((f - ‖q‖ ^ 2) / b + 6 * b * (1 - τ * b))
        (30 * v ^ 2 * (1 - 2 * σ * v + v ^ 2))
        (30 * b ^ 2 * (1 - 2 * τ * b + b ^ 2)) p q =
      scalarHessianCorrection v b σ τ e B (‖p‖ ^ 2) +
      scalarHessianCorrection b v τ σ f C (‖q‖ ^ 2) +
      quarticNormLoss v b e f p q + radialQuadraticTerm v b p q +
      zeroOrderIntegrand v b σ τ := by
  rw [← scalar_potential_identity]
  unfold scalarCouplingTerm scalarHessianCorrection quarticNormLoss radialQuadraticTerm
  ring

theorem axial_plus_radial_identity (v b : ℝ) (p q : Vec) :
    (axialCoefficient v b + 2 * kappa v b / (3 * v)) * ‖p‖ ^ 2 +
      (axialCoefficient b v + 2 * kappa b v / (3 * b)) * ‖q‖ ^ 2 +
      radialQuadraticTerm v b p q =
    quadraticCoefficient v b * ‖p‖ ^ 2 +
      2 * mixedCoefficient v b * inner ℝ p q +
      quadraticCoefficient b v * ‖q‖ ^ 2 := by
  unfold radialQuadraticTerm quadraticCoefficient mixedCoefficient denominator
  rw [norm_sub_sq_real]
  have hd : 4 + b ^ 2 + v ^ 2 = 4 + v ^ 2 + b ^ 2 := by ring
  rw [hd]
  ring

/-- The actual invariant Hessian expression and the scalar correction
are bounded together, so the axial reduction uses the same spectral data. -/
theorem invariant_axial_bound (A U : Mat) (Z : Angular.Gradient)
    (S : Shape) (τ : ℝ) (p' k l p : Vec)
    (hv : 0 < normalizedBlockNorm A)
    (hsum : normalizedBlockNorm A + normalizedBlockNorm U ≤ 2) (hτ : τ ≤ 1)
    (he : (parameters S p' k l).squaredNorm / 6 = weylGradientEnergy Z)
    (hp : ‖p'‖ ^ 2 = ‖p‖ ^ 2)
    (hB : weylMatrixEnergy A Z =
      curvatureContraction S (normalizedBlockNorm A) (parameters S p' k l))
    (hH : invariantHessianForm A U Z ≤
      hessianTensorForm S (normalizedBlockNorm A) (normalizedBlockNorm U) p' k l) :
    weight (normalizedBlockNorm A) (normalizedBlockNorm U) * invariantHessianForm A U Z +
      scalarHessianCorrection (normalizedBlockNorm A) (normalizedBlockNorm U)
        S.sigma τ (weylGradientEnergy Z) (weylMatrixEnergy A Z) (‖p‖ ^ 2) ≤
    (axialCoefficient (normalizedBlockNorm A) (normalizedBlockNorm U) +
        2 * kappa (normalizedBlockNorm A) (normalizedBlockNorm U) /
          (3 * normalizedBlockNorm A)) * ‖p‖ ^ 2 := by
  have hh := hessian_quadratic_axial_bound S hv (normalizedBlockNorm_nonneg U) hsum hτ p' k l
  have hm := mul_le_mul_of_nonneg_left hH
    (show 0 ≤ weight (normalizedBlockNorm A) (normalizedBlockNorm U) by unfold weight; positivity)
  unfold hessianQuadraticContribution at hh
  rw [he, ← hB, hp] at hh
  unfold scalarHessianCorrection
  linarith only [hh, hm]

theorem scalarWeight_positive {v b : ℝ} (_hv : 0 ≤ v) (hb : 0 ≤ b)
    (hsum : v + b ≤ 2) : 0 < scalarWeight v b := by
  unfold scalarWeight
  linarith

/-- The two cubic and projection upper bounds have exactly the quartic
energy form used by the scalar relaxation. -/
theorem quartic_bounds_identity (v b r s σ τ ρ χ e f : ℝ) (p q : Vec) :
    (1 / 2 : ℝ) * Real.sqrt (3 / 5) * (‖p‖ + ‖q‖) * scalarWeight v b *
        (e * Real.sqrt e) +
      (1 / 2 : ℝ) * Real.sqrt (3 / 5) * (‖p‖ + ‖q‖) * scalarWeight b v *
        (f * Real.sqrt f) +
      (9 / 64 : ℝ) * (‖p‖ + ‖q‖) ^ 2 * projectionBracket v (b * s) σ ρ e (‖p‖ ^ 2) +
      (9 / 64 : ℝ) * (‖p‖ + ‖q‖) ^ 2 * projectionBracket b (v * r) τ χ f (‖q‖ ^ 2) +
      quarticNormLoss v b e f p q =
    quarticEnergy v b ((5 / 3) * ‖p‖ ^ 2) ((5 / 3) * ‖q‖ ^ 2)
      (projectionCoefficient v (b * s) σ ρ) (projectionCoefficient b (v * r) τ χ)
      (defectCoefficient v (b * s)) (defectCoefficient b (v * r)) e f := by
  unfold quarticEnergy
  rw [gradientSum_radial]
  unfold projectionBracket quarticNormLoss
  ring

end
end PositiveEinsteinFour.QuaternionFrame
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

namespace PointwiseSpectrum

variable {A U : Mat} {Z : Angular.Gradient} {p : Vec}

theorem energy_lower (D : PointwiseSpectrum A U Z p) :
    (5 / 3 : ℝ) * ‖p‖ ^ 2 ≤ weylGradientEnergy Z := by
  have h := D.energy
  rw [parameters_energy, D.radial_norm] at h
  nlinarith only [h, sq_nonneg ‖D.second‖, sq_nonneg ‖D.third‖]

theorem shape_sigma_upper (D : PointwiseSpectrum A U Z p) : D.shape.sigma ≤ 1 := by
  nlinarith only [D.shape.sigma_rho_circle, sq_nonneg D.shape.rho]

theorem minimum_shift (D : PointwiseSpectrum A U Z p) :
    (A + (normalizedBlockNorm A * D.minimum) • (1 : Mat)).PosSemidef :=
  shape_minimum_shift_posSemidef A D.frame D.orthogonal D.shape _ D.minimum
    (normalizedBlockNorm_nonneg A) D.diagonal D.spectrum_lower

theorem scalar_norm (D : PointwiseSpectrum A U Z p) (hv : 0 < normalizedBlockNorm A) :
    scalarNormExpression 0 A Z =
      (weylGradientEnergy Z - ‖p‖ ^ 2) / normalizedBlockNorm A +
        6 * normalizedBlockNorm A * (1 - D.shape.sigma * normalizedBlockNorm A) := by
  rw [scalarNormExpression_spectral A D.frame D.orthogonal D.shape Z hv D.diagonal,
    D.original_radial_norm]

theorem trace_energy (D : PointwiseSpectrum A U Z p) :
    traceEnergy A = 30 * normalizedBlockNorm A ^ 2 *
      (1 - 2 * D.shape.sigma * normalizedBlockNorm A + normalizedBlockNorm A ^ 2) :=
  traceEnergy_spectral A D.frame D.orthogonal D.shape _ D.diagonal

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

namespace PointwiseSpectrum

variable {A U : Mat} {Z : Angular.Gradient} {p : Vec}

theorem scalar_norm_closed (D : PointwiseSpectrum A U Z p)
    (hzero : normalizedBlockNorm A = 0 → Z = 0) :
    scalarNormExpression 0 A Z =
      (weylGradientEnergy Z - ‖p‖ ^ 2) / normalizedBlockNorm A +
        6 * normalizedBlockNorm A * (1 - D.shape.sigma * normalizedBlockNorm A) := by
  by_cases hv : normalizedBlockNorm A = 0
  · have hAz : A = 0 := (normalizedBlockNorm_eq_zero_iff A).mp hv
    have hz := hzero hv
    have he : weylGradientEnergy Z = 0 := by rw [hz, zero_gradient_energy]
    have hleft : scalarNormExpression 0 A Z = 0 := by
      rw [hz]
      simp [scalarNormExpression, regularizedRadialDerivative, hAz, zero_gradient_energy]
    rw [hleft, he, hv]
    simp
  · exact D.scalar_norm (lt_of_le_of_ne (normalizedBlockNorm_nonneg A) (Ne.symm hv))

theorem axial_closed (D : PointwiseSpectrum A U Z p)
    (hzero : normalizedBlockNorm A = 0 → Z = 0)
    (hsum : normalizedBlockNorm A + normalizedBlockNorm U ≤ 2)
    {τ : ℝ} (hτ : τ ≤ 1) :
    weight (normalizedBlockNorm A) (normalizedBlockNorm U) * invariantHessianForm A U Z +
      scalarHessianCorrection (normalizedBlockNorm A) (normalizedBlockNorm U)
        D.shape.sigma τ (weylGradientEnergy Z) (weylMatrixEnergy A Z) (‖p‖ ^ 2) ≤
    (axialCoefficient (normalizedBlockNorm A) (normalizedBlockNorm U) +
        2 * kappa (normalizedBlockNorm A) (normalizedBlockNorm U) /
          (3 * normalizedBlockNorm A)) * ‖p‖ ^ 2 := by
  by_cases hv : normalizedBlockNorm A = 0
  · have hz := hzero hv
    have he0 : weylGradientEnergy Z = 0 := by rw [hz, zero_gradient_energy]
    have hB0 : weylMatrixEnergy A Z = 0 := by rw [hz, zero_gradient_matrix_energy]
    have hp : ‖p‖ ^ 2 = 0 := by
      have he := D.energy_lower
      rw [he0] at he
      nlinarith only [he, sq_nonneg ‖p‖]
    have hh : invariantHessianForm A U Z ≤ 0 := by
      rw [hz]
      exact zero_gradient_hessian_nonpos A U
    have hm := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ weight (normalizedBlockNorm A) (normalizedBlockNorm U) by unfold weight; positivity)
    rw [he0, hB0, hp, hv]
    simpa [scalarHessianCorrection, hv] using hm
  · exact invariant_axial_bound A U Z D.shape τ D.radial D.second D.third p
      (lt_of_le_of_ne (normalizedBlockNorm_nonneg A) (Ne.symm hv)) hsum hτ
      D.energy D.radial_norm D.matrix_energy D.hessian

end PointwiseSpectrum

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

theorem arrayCoupledIntegrand_le_reduced_oai
    (A U : Mat) (Z V : Angular.Gradient) (a ab p q : Vec)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (hZs : ∀ i, symmetric (Z i)) (hZt : ∀ i, traceFree (Z i))
    (hZb : ∀ r i, gradientDivergence Z r i = 0)
    (hVs : ∀ i, symmetric (V i)) (hVt : ∀ i, traceFree (V i))
    (hVb : ∀ r i, gradientDivergence V r i = 0)
    (hzero : normalizedBlockNorm A = 0 → Z = 0)
    (hzerob : normalizedBlockNorm U = 0 → V = 0)
    (D : PointwiseSpectrum A U Z p) (F : PointwiseSpectrum U A V q)
    (hmin : normalizedBlockNorm A * D.minimum + normalizedBlockNorm U * F.minimum ≤ 2)
    (ha : ‖a‖ ^ 2 = (9 / 16 : ℝ) * scalarWeight (normalizedBlockNorm A) (normalizedBlockNorm U) ^ 2 *
      ‖p - q‖ ^ 2)
    (hab : ‖ab‖ ^ 2 = (9 / 16 : ℝ) * scalarWeight (normalizedBlockNorm U) (normalizedBlockNorm A) ^ 2 *
      ‖p - q‖ ^ 2) :
    arrayCoupledIntegrand A U Z V a ab p q ≤
      reducedIntegrand (normalizedBlockNorm A) (normalizedBlockNorm U) D.minimum F.minimum
        D.shape.sigma F.shape.sigma D.shape.rho F.shape.rho
        (weylGradientEnergy Z) (weylGradientEnergy V) p q := by
  let v := normalizedBlockNorm A
  let b := normalizedBlockNorm U
  have hv0 : 0 ≤ v := normalizedBlockNorm_nonneg A
  have hb0 : 0 ≤ b := normalizedBlockNorm_nonneg U
  have hsum : v + b ≤ 2 := by
    have hr : v ≤ v * D.minimum := by nlinarith only [hv0, D.minimum_lower]
    have hs : b ≤ b * F.minimum := by nlinarith only [hb0, F.minimum_lower]
    linarith only [hmin, hr, hs]
  have hv2 : v ≤ 2 := by linarith only [hsum, hb0]
  have hb2 : b ≤ 2 := by linarith only [hsum, hv0]
  have hM := scalarWeight_positive hv0 hb0 hsum
  have hMb := scalarWeight_positive hb0 hv0 (show b + v ≤ 2 by linarith only [hsum])
  have hab' : ‖ab‖ ^ 2 = (9 / 16 : ℝ) * scalarWeight b v ^ 2 * ‖q - p‖ ^ 2 := by
    rw [norm_sub_rev q p]
    exact hab
  have hc := cubic_bound_of_weight_square (scalarWeight v b) hM.le a p q ha Z hZs hZt hZb
  have hcb := cubic_bound_of_weight_square (scalarWeight b v) hMb.le ab q p hab' V hVs hVt hVb
  have hnormsum : ‖q‖ + ‖p‖ = ‖p‖ + ‖q‖ := add_comm _ _
  rw [hnormsum] at hcb
  have hcost := projection_bound_of_weight_square A U hA hU htA htU
    (v * D.minimum) (b * F.minimum) D.minimum_shift F.minimum_shift hmin
    (scalarWeight v b) (ne_of_gt hM) a p q ha Z hZs hZt hZb
    D.shape D.radial D.second D.third D.energy D.radial_norm D.matrix_energy
  have hcostb := projection_bound_of_weight_square U A hU hA htU htA
    (b * F.minimum) (v * D.minimum) F.minimum_shift D.minimum_shift
    (by linarith only [hmin]) (scalarWeight b v) (ne_of_gt hMb) ab q p hab' V hVs hVt hVb
    F.shape F.radial F.second F.third F.energy F.radial_norm F.matrix_energy
  have hcost' := hcost.trans (projection_bound_norm_sum p q hv0 hv2
    (mul_nonneg hb0 (by linarith only [F.minimum_lower])) D.shape_sigma_upper D.energy_lower)
  have hcostb' := hcostb.trans (projection_bound_norm_sum q p hb0 hb2
    (mul_nonneg hv0 (by linarith only [D.minimum_lower])) F.shape_sigma_upper F.energy_lower)
  rw [hnormsum] at hcostb'
  have hx := D.axial_closed hzero hsum F.shape_sigma_upper
  have hy := F.axial_closed hzerob (by linarith only [hsum]) D.shape_sigma_upper
  have hcostWeight :
      generalCurvaturePairing A U
          (highestProjection (weightTensor a (gradientTensor Z)))
          (highestProjection (weightTensor a (gradientTensor Z))) / (24 * weight v b) ≤
        (9 / 64 : ℝ) * (‖p‖ + ‖q‖) ^ 2 *
          projectionBracket v (b * F.minimum) D.shape.sigma D.shape.rho
            (weylGradientEnergy Z) (‖p‖ ^ 2) := by
    simpa only [weight, scalarWeight] using hcost'
  have hcostWeightb :
      generalCurvaturePairing U A
          (highestProjection (weightTensor ab (gradientTensor V)))
          (highestProjection (weightTensor ab (gradientTensor V))) / (24 * weight b v) ≤
        (9 / 64 : ℝ) * (‖p‖ + ‖q‖) ^ 2 *
          projectionBracket b (v * D.minimum) F.shape.sigma F.shape.rho
            (weylGradientEnergy V) (‖q‖ ^ 2) := by
    simpa only [weight, scalarWeight] using hcostb'
  have hfour :
      (-(5 / 36 : ℝ) * weightedCubicField a Z +
        generalCurvaturePairing A U
          (highestProjection (weightTensor a (gradientTensor Z)))
          (highestProjection (weightTensor a (gradientTensor Z))) / (24 * weight v b)) +
      (-(5 / 36 : ℝ) * weightedCubicField ab V +
        generalCurvaturePairing U A
          (highestProjection (weightTensor ab (gradientTensor V)))
          (highestProjection (weightTensor ab (gradientTensor V))) / (24 * weight b v)) +
      quarticNormLoss v b (weylGradientEnergy Z) (weylGradientEnergy V) p q ≤
      quarticEnergy v b ((5 / 3) * ‖p‖ ^ 2) ((5 / 3) * ‖q‖ ^ 2)
        (projectionCoefficient v (b * F.minimum) D.shape.sigma D.shape.rho)
        (projectionCoefficient b (v * D.minimum) F.shape.sigma F.shape.rho)
        (defectCoefficient v (b * F.minimum)) (defectCoefficient b (v * D.minimum))
        (weylGradientEnergy Z) (weylGradientEnergy V) := by
    rw [← quartic_bounds_identity]
    linarith only [hc, hcb, hcostWeight, hcostWeightb]
  have hsplit : arrayCoupledIntegrand A U Z V a ab p q =
      (weight v b * invariantHessianForm A U Z +
        scalarHessianCorrection v b D.shape.sigma F.shape.sigma
          (weylGradientEnergy Z) (weylMatrixEnergy A Z) (‖p‖ ^ 2)) +
      (weight b v * invariantHessianForm U A V +
        scalarHessianCorrection b v F.shape.sigma D.shape.sigma
          (weylGradientEnergy V) (weylMatrixEnergy U V) (‖q‖ ^ 2)) +
      ((-(5 / 36 : ℝ) * weightedCubicField a Z +
        generalCurvaturePairing A U
          (highestProjection (weightTensor a (gradientTensor Z)))
          (highestProjection (weightTensor a (gradientTensor Z))) / (24 * weight v b)) +
       (-(5 / 36 : ℝ) * weightedCubicField ab V +
        generalCurvaturePairing U A
          (highestProjection (weightTensor ab (gradientTensor V)))
          (highestProjection (weightTensor ab (gradientTensor V))) / (24 * weight b v)) +
        quarticNormLoss v b (weylGradientEnergy Z) (weylGradientEnergy V) p q) +
      radialQuadraticTerm v b p q + zeroOrderIntegrand v b D.shape.sigma F.shape.sigma := by
    unfold arrayCoupledIntegrand arrayHessianTerm
    rw [D.scalar_norm_closed hzero, F.scalar_norm_closed hzerob, D.trace_energy, F.trace_energy,
      scalarCouplingTerm_spectral_split]
    ring
  rw [hsplit]
  unfold reducedIntegrand
  have htwo := axial_plus_radial_identity v b p q
  linarith only [hx, hy, hfour, htwo]

end
end PositiveEinsteinFour.QuaternionFrame
end


end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.QuaternionFrame.arrayCoupledIntegrand_le_reduced_oai := @OAI.PositiveEinsteinFour.QuaternionFrame.arrayCoupledIntegrand_le_reduced_oai
