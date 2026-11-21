-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_secondMax_le_candidateMaximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:57:19.336965+00:00
-- url     : https://prove2.me/submissions/ca765298-cbd5-430e-8e31-22aa6fe63a28

module
public import Definitions.Def_NewtonianLipschitz_JacobianNormalization
public import Definitions.Def_NewtonianLipschitz_JacobianAxisBounds
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_three
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_cycle_rowSum
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_firstMax_le_candidateMaximum
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
    (hx1 : 0 < x 1)
    (hx00 : 0 ≤ x 0) (hx0 : x 0 ≤ x 1)
    (hx20 : 0 ≤ x 2) (hx2 : x 2 ≤ x 1) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ x i j|) ≤
      (1 / (x 1) ^ 3) * (μ * candidateMaximum) := by
  have hy0 : 0 < (cycleVec x) 0 := by
    simpa only [cycleVec_zero] using hx1
  have hy10 : 0 ≤ (cycleVec x) 1 := by
    simpa only [cycleVec_one] using hx20
  have hy1 : (cycleVec x) 1 ≤ (cycleVec x) 0 := by
    simpa only [cycleVec_one, cycleVec_zero] using hx2
  have hy20 : 0 ≤ (cycleVec x) 2 := by
    simpa only [cycleVec_two] using hx00
  have hy2 : (cycleVec x) 2 ≤ (cycleVec x) 0 := by
    simpa only [cycleVec_two, cycleVec_zero] using hx0
  have hbound :=
    newtonianJacobianMatrix_firstMax_le_candidateMaximum
      μ (cycleVec x) (cycleIndex (cycleIndex i))
      hμ hy0 hy10 hy1 hy20 hy2
  rw [newtonianJacobianMatrix_cycle_rowSum
    μ x (cycleIndex (cycleIndex i)),
    cycleIndex_three i] at hbound
  simpa only [cycleVec_zero] using hbound
end NewtonianLipschitz
