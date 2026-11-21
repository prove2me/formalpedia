-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_first_safe_axis_tangent_columns_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:05:48.447317+00:00
-- url     : https://prove2.me/submissions/6ad9a488-06dd-4bf4-9bac-a852d4da2f62

module
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialNormalized
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialFirstAxis
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_cons
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_nil
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_entry_abs_coordinateAbs
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_entry_positive_smul
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_tangent_columns_le
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_one
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_two
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_zero
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_positive_first_coordinate_normalization
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
    (μ d : ℝ) (x : Vec3) (k : Fin 3)
    (hμ : 0 ≤ μ) (hd : 0 < d) (hx : d ≤ |x 0|) :
    |newtonianJacobianMatrix μ x k 1| +
        |newtonianJacobianMatrix μ x k 2| ≤
      (1 / d ^ 3) * (μ * (5 / 4 : ℝ)) := by
  let z : Vec3 := coordinateAbs x
  have hzi (i : Fin 3) : z i = |x i| := by
    exact coordinateAbs_apply x i
  have hza : d ≤ z 0 := by
    rwa [hzi]
  have ha : 0 < z 0 := lt_of_lt_of_le hd hza
  let u : ℝ := z 1 / z 0
  let v : ℝ := z 2 / z 0
  have hu : 0 ≤ u :=
    div_nonneg (by rw [hzi]; exact abs_nonneg _) ha.le
  have hv : 0 ≤ v :=
    div_nonneg (by rw [hzi]; exact abs_nonneg _) ha.le
  have hnormal :
      (z 0) • normalizedVector u v = z := by
    exact positive_first_coordinate_normalization z ha
  have hz_nonzero : normalizedVector u v ≠ 0 := by
    intro hz
    have h := congrArg (fun q : Vec3 => q 0) hz
    simp only [normalizedVector_zero, Pi.zero_apply] at h
    norm_num at h
  have hfactor : 0 ≤ (1 : ℝ) / (z 0) ^ 3 := by
    positivity
  have hinv : (1 : ℝ) / (z 0) ^ 3 ≤ 1 / d ^ 3 := by
    have hpow : d ^ 3 ≤ (z 0) ^ 3 :=
      pow_le_pow_left₀ hd.le hza 3
    apply (div_le_div_iff₀ (pow_pos ha 3) (pow_pos hd 3)).2
    simpa only [one_mul] using hpow
  have hentry (j : Fin 3) :
      |newtonianJacobianMatrix μ x k j| =
        (1 / (z 0) ^ 3) *
          |newtonianJacobianMatrix μ (normalizedVector u v) k j| := by
    calc
      |newtonianJacobianMatrix μ x k j| =
          |newtonianJacobianMatrix μ z k j| := by
        exact (newtonianJacobianMatrix_entry_abs_coordinateAbs μ x k j).symm
      _ = |newtonianJacobianMatrix μ
              ((z 0) • normalizedVector u v) k j| := by
        rw [hnormal]
      _ = |(1 / (z 0) ^ 3) *
              newtonianJacobianMatrix μ (normalizedVector u v) k j| := by
        rw [newtonianJacobianMatrix_entry_positive_smul
          μ (z 0) (normalizedVector u v) k j ha hz_nonzero]
      _ = (1 / (z 0) ^ 3) *
            |newtonianJacobianMatrix μ (normalizedVector u v) k j| := by
        rw [abs_mul, abs_of_nonneg hfactor]
  have hnormbound :
      |newtonianJacobianMatrix μ (normalizedVector u v) k 1| +
        |newtonianJacobianMatrix μ (normalizedVector u v) k 2| ≤
          μ * (5 / 4 : ℝ) :=
    newtonianJacobianMatrix_normalized_tangent_columns_le
      μ u v hμ hu hv k
  calc
    |newtonianJacobianMatrix μ x k 1| +
        |newtonianJacobianMatrix μ x k 2| =
          (1 / (z 0) ^ 3) *
            (|newtonianJacobianMatrix μ (normalizedVector u v) k 1| +
              |newtonianJacobianMatrix μ (normalizedVector u v) k 2|) := by
      rw [hentry 1, hentry 2]
      ring
    _ ≤ (1 / (z 0) ^ 3) * (μ * (5 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hnormbound hfactor
    _ ≤ (1 / d ^ 3) * (μ * (5 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_right hinv
        (mul_nonneg hμ (by norm_num))
end NewtonianLipschitz
