-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_normalized_tangent_columns_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:03:44.103397+00:00
-- url     : https://prove2.me/submissions/8dd7fb43-8aa1-4fe5-9298-03d0b086853d

module
public import Definitions.Def_NewtonianLipschitz_SafePlaneReduction
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialNormalized
public import Theorems.Thm_NewtonianLipschitz_tangential_normalized_radius_bounds
public import Theorems.Thm_NewtonianLipschitz_tangential_normalized_first_numerator_le_radius
public import Theorems.Thm_NewtonianLipschitz_tangential_normalized_lateral_numerator_le_radius
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_cons
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_nil
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_coordinates
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_one_one
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_one_two
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_two_one
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_two_two
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_zero_one
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_zero_two
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_one
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_two
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_zero
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_one
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_two
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_zero
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_one
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_two
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_zero
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_cons
attribute [local simp] NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_nil
attribute [local simp] NewtonianLipschitz.coordinateAbs_apply
attribute [local simp] NewtonianLipschitz.cycleIndex_one
attribute [local simp] NewtonianLipschitz.cycleIndex_two
attribute [local simp] NewtonianLipschitz.cycleIndex_zero
attribute [local simp] NewtonianLipschitz.cycleVec_one
attribute [local simp] NewtonianLipschitz.cycleVec_two
attribute [local simp] NewtonianLipschitz.cycleVec_zero
attribute [local simp] NewtonianLipschitz.normalizedVector_one
attribute [local simp] NewtonianLipschitz.normalizedVector_two
attribute [local simp] NewtonianLipschitz.normalizedVector_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.swapYZIndex_one
attribute [local simp] NewtonianLipschitz.swapYZIndex_two
attribute [local simp] NewtonianLipschitz.swapYZIndex_zero
attribute [local simp] NewtonianLipschitz.swapYZVec_one
attribute [local simp] NewtonianLipschitz.swapYZVec_two
attribute [local simp] NewtonianLipschitz.swapYZVec_zero
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero



set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (μ u v : ℝ) (hμ : 0 ≤ μ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (k : Fin 3) :
    |newtonianJacobianMatrix μ (normalizedVector u v) k 1| +
      |newtonianJacobianMatrix μ (normalizedVector u v) k 2| ≤
        μ * (5 / 4 : ℝ) := by
  let r := euclideanRadius (normalizedVector u v)
  have hr1 : 1 ≤ r :=
    (tangential_normalized_radius_bounds u v).1
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  have hK : 0 ≤ μ / r ^ 5 := by
    exact div_nonneg hμ (pow_nonneg hrpos.le _)
  have hcancel :
      (μ / r ^ 5) * ((5 / 4 : ℝ) * r ^ 5) =
        μ * (5 / 4 : ℝ) := by
    field_simp [ne_of_gt hrpos] <;> ring
  fin_cases k
  · have hrow :
        |newtonianJacobianMatrix μ (normalizedVector u v) 0 1| +
          |newtonianJacobianMatrix μ (normalizedVector u v) 0 2| =
            (μ / r ^ 5) * (3 * (u + v)) := by
      rw [newtonianJacobianMatrix_normalized_zero_one,
        newtonianJacobianMatrix_normalized_zero_two]
      change |(μ / r ^ 5) * (3 * u)| +
          |(μ / r ^ 5) * (3 * v)| =
          (μ / r ^ 5) * (3 * (u + v))
      simp only [abs_mul, abs_of_nonneg hK,
        abs_of_nonneg hu, abs_of_nonneg hv,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    calc
      _ = (μ / r ^ 5) * (3 * (u + v)) := hrow
      _ ≤ (μ / r ^ 5) * ((5 / 4 : ℝ) * r ^ 5) :=
        mul_le_mul_of_nonneg_left
          (tangential_normalized_first_numerator_le_radius u v hu hv) hK
      _ = μ * (5 / 4 : ℝ) := hcancel
  · have hrow :
        |newtonianJacobianMatrix μ (normalizedVector u v) 1 1| +
          |newtonianJacobianMatrix μ (normalizedVector u v) 1 2| =
            (μ / r ^ 5) *
              (|2 * u ^ 2 - 1 - v ^ 2| + 3 * u * v) := by
      rw [newtonianJacobianMatrix_normalized_one_one,
        newtonianJacobianMatrix_normalized_one_two]
      change |(μ / r ^ 5) * (2 * u ^ 2 - 1 - v ^ 2)| +
          |(μ / r ^ 5) * (3 * u * v)| =
          (μ / r ^ 5) * (|2 * u ^ 2 - 1 - v ^ 2| + 3 * u * v)
      simp only [abs_mul, abs_of_nonneg hK,
        abs_of_nonneg hu, abs_of_nonneg hv,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    calc
      _ = (μ / r ^ 5) *
            (|2 * u ^ 2 - 1 - v ^ 2| + 3 * u * v) := hrow
      _ ≤ (μ / r ^ 5) * ((5 / 4 : ℝ) * r ^ 5) :=
        mul_le_mul_of_nonneg_left
          (tangential_normalized_lateral_numerator_le_radius u v hu hv) hK
      _ = μ * (5 / 4 : ℝ) := hcancel
  · have hrow :
        |newtonianJacobianMatrix μ (normalizedVector u v) 2 1| +
          |newtonianJacobianMatrix μ (normalizedVector u v) 2 2| =
            (μ / r ^ 5) *
              (|2 * v ^ 2 - 1 - u ^ 2| + 3 * v * u) := by
      rw [newtonianJacobianMatrix_normalized_two_one,
        newtonianJacobianMatrix_normalized_two_two]
      change |(μ / r ^ 5) * (3 * v * u)| +
          |(μ / r ^ 5) * (2 * v ^ 2 - 1 - u ^ 2)| =
          (μ / r ^ 5) * (|2 * v ^ 2 - 1 - u ^ 2| + 3 * v * u)
      simp only [abs_mul, abs_of_nonneg hK,
        abs_of_nonneg hu, abs_of_nonneg hv,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    have hlat :
        |2 * v ^ 2 - 1 - u ^ 2| + 3 * v * u ≤
          (5 / 4 : ℝ) * r ^ 5 := by
      have ht :=
        tangential_normalized_lateral_numerator_le_radius v u hv hu
      rw [show euclideanRadius (normalizedVector v u) =
        r by
          dsimp [r]
          rw [euclideanRadius_eq_coordinates,
              euclideanRadius_eq_coordinates]
          simp only [normalizedVector_zero, normalizedVector_one,
            normalizedVector_two]
          congr 1
          ring] at ht
      exact ht
    calc
      _ = (μ / r ^ 5) *
            (|2 * v ^ 2 - 1 - u ^ 2| + 3 * v * u) := hrow
      _ ≤ (μ / r ^ 5) * ((5 / 4 : ℝ) * r ^ 5) :=
        mul_le_mul_of_nonneg_left hlat hK
      _ = μ * (5 / 4 : ℝ) := hcancel
end NewtonianLipschitz
