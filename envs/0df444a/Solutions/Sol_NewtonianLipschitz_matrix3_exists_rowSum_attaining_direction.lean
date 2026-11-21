-- Prove2me | solution 1 for NewtonianLipschitz.matrix3_exists_rowSum_attaining_direction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:35:43.953444+00:00
-- url     : https://prove2.me/submissions/a9c64850-7a8d-420f-a1e6-c83760a07ff1

module
public import Definitions.Def_NewtonianLipschitz_JacobianSharpWitness
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorWitness
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
    (A : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    ∃ h : Vec3, ‖h‖ ≤ 1 ∧
      (A *ᵥ h) i = ∑ j : Fin 3, |A i j| := by
  let h : Vec3 := fun j => if 0 ≤ A i j then (1 : ℝ) else -1
  have hnorm : ‖h‖ ≤ (1 : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
    intro j
    change ‖if 0 ≤ A i j then (1 : ℝ) else -1‖ ≤ 1
    split_ifs <;> norm_num
  refine ⟨h, hnorm, ?_⟩
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  change A i j * (if 0 ≤ A i j then (1 : ℝ) else -1) =
    |A i j|
  split_ifs with hsign
  · simpa only [mul_one, abs_of_nonneg hsign]
  · have hneg : A i j ≤ 0 := le_of_lt (lt_of_not_ge hsign)
    rw [abs_of_nonpos hneg]
    ring
end NewtonianLipschitz
