-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_firstMax_le_candidateMaximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:55:38.858415+00:00
-- url     : https://prove2.me/submissions/690031a8-4fb5-46b6-a16f-5c8ccae76bb7

module
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
public import Definitions.Def_NewtonianLipschitz_JacobianNormalization
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_rowSum_positive_smul
public import Theorems.Thm_NewtonianLipschitz_positive_first_coordinate_normalization
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_allRows_le_candidateMaximum
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
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (μ : ℝ) (x : Vec3) (i : Fin 3)
    (hμ : 0 ≤ μ)
    (hx0 : 0 < x 0)
    (hx10 : 0 ≤ x 1) (hx1 : x 1 ≤ x 0)
    (hx20 : 0 ≤ x 2) (hx2 : x 2 ≤ x 0) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ x i j|) ≤
      (1 / (x 0) ^ 3) * (μ * candidateMaximum) := by
  let u : ℝ := x 1 / x 0
  let v : ℝ := x 2 / x 0
  let z : Vec3 := normalizedVector u v
  have hu0 : 0 ≤ u := div_nonneg hx10 hx0.le
  have hu1 : u ≤ 1 := (div_le_iff₀ hx0).2 (by simpa only [one_mul] using hx1)
  have hv0 : 0 ≤ v := div_nonneg hx20 hx0.le
  have hv1 : v ≤ 1 := (div_le_iff₀ hx0).2 (by simpa only [one_mul] using hx2)
  have hz : z ≠ 0 := by
    intro hzero
    have hfirst := congrArg (fun w : Vec3 => w 0) hzero
    simp only [z, normalizedVector_zero, Pi.zero_apply] at hfirst
    norm_num at hfirst
  have hvec : (x 0) • z = x :=
    positive_first_coordinate_normalization x hx0
  have hnorm :=
    newtonianJacobianMatrix_normalized_allRows_le_candidateMaximum
      μ u v hμ hu0 hu1 hv0 hv1 i
  calc
    (∑ j : Fin 3, |newtonianJacobianMatrix μ x i j|)
      = ∑ j : Fin 3,
          |newtonianJacobianMatrix μ ((x 0) • z) i j| := by
        rw [hvec]
    _ = (1 / (x 0) ^ 3) *
          (∑ j : Fin 3, |newtonianJacobianMatrix μ z i j|) :=
        newtonianJacobianMatrix_rowSum_positive_smul
          μ (x 0) z i hx0 hz
    _ ≤ (1 / (x 0) ^ 3) * (μ * candidateMaximum) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
end NewtonianLipschitz
