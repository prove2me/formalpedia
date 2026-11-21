-- Prove2me | solution 1 for NewtonianLipschitz.matrix3_mulVec_tangent_two_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:00:58.097414+00:00
-- url     : https://prove2.me/submissions/b04d8a04-7c40-4bf1-9800-9b738e8f8673

module
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialFirstAxis
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialAllAxes
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_cons
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_nil
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
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
    (A : Matrix (Fin 3) (Fin 3) ℝ) (h : Vec3)
    (hzero : h 2 = 0) (B : ℝ) (hB : 0 ≤ B)
    (hrows : ∀ k : Fin 3, |A k 0| + |A k 1| ≤ B) :
    ‖A *ᵥ h‖ ≤ B * ‖h‖ := by
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg hB (norm_nonneg h))).2
  intro k
  have h0 : |h 0| ≤ ‖h‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm h (0 : Fin 3))
  have h1 : |h 1| ≤ ‖h‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm h (1 : Fin 3))
  have hterm0 : |A k 0 * h 0| ≤ |A k 0| * ‖h‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h0 (abs_nonneg _)
  have hterm1 : |A k 1 * h 1| ≤ |A k 1| * ‖h‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hbound : |(A *ᵥ h) k| ≤ (|A k 0| + |A k 1|) * ‖h‖ := by
    calc
      |(A *ᵥ h) k| = |A k 0 * h 0 + A k 1 * h 1| := by
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
          hzero, mul_zero, add_zero]
      _ ≤ |A k 0 * h 0| + |A k 1 * h 1| :=
        abs_add_le _ _
      _ ≤ |A k 0| * ‖h‖ + |A k 1| * ‖h‖ :=
        add_le_add hterm0 hterm1
      _ = (|A k 0| + |A k 1|) * ‖h‖ := by ring
  calc
    ‖(A *ᵥ h) k‖ = |(A *ᵥ h) k| := Real.norm_eq_abs _
    _ ≤ (|A k 0| + |A k 1|) * ‖h‖ := hbound
    _ ≤ B * ‖h‖ :=
      mul_le_mul_of_nonneg_right (hrows k) (norm_nonneg h)
end NewtonianLipschitz
