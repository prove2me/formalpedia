-- Prove2me | solution 2 for NewtonianLipschitz.matrix3_mulVec_coordinate_abs_le_rowSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:53:54.854026+00:00
-- url     : https://prove2.me/submissions/23c9d479-2b08-4a68-bd75-9fe192e4ff65

module
public import Definitions.Def_NewtonianLipschitz_JacobianCartesianBound
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorAction
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
    (A : Matrix (Fin 3) (Fin 3) ℝ) (h : Vec3) (i : Fin 3) :
    |(A *ᵥ h) i| ≤ (∑ j : Fin 3, |A i j|) * ‖h‖ := by
  have hterm (j : Fin 3) :
      |A i j * h j| ≤ |A i j| * ‖h‖ := by
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm h j))
      (abs_nonneg _)
  have htri :
      |A i 0 * h 0 + A i 1 * h 1 + A i 2 * h 2| ≤
        |A i 0 * h 0| + |A i 1 * h 1| +
          |A i 2 * h 2| := by
    have hfirst :=
      abs_add_le (A i 0 * h 0 + A i 1 * h 1) (A i 2 * h 2)
    have hsecond := abs_add_le (A i 0 * h 0) (A i 1 * h 1)
    linarith
  have hbound :
      |A i 0 * h 0 + A i 1 * h 1 + A i 2 * h 2| ≤
        (|A i 0| + |A i 1| + |A i 2|) * ‖h‖ := by
    calc
      |A i 0 * h 0 + A i 1 * h 1 + A i 2 * h 2|
        ≤ |A i 0 * h 0| + |A i 1 * h 1| +
            |A i 2 * h 2| := htri
      _ ≤ |A i 0| * ‖h‖ + |A i 1| * ‖h‖ +
            |A i 2| * ‖h‖ := by
          exact add_le_add (add_le_add (hterm 0) (hterm 1))
            (hterm 2)
      _ = (|A i 0| + |A i 1| + |A i 2|) * ‖h‖ := by
          ring
  simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    using hbound
end NewtonianLipschitz
