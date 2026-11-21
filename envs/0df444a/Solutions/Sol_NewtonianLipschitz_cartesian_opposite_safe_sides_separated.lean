-- Prove2me | solution 1 for NewtonianLipschitz.cartesian_opposite_safe_sides_separated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:59:05.626861+00:00
-- url     : https://prove2.me/submissions/0240b5dd-554a-4fbe-a2b7-6ecd120cc93f

module
public import Definitions.Def_NewtonianLipschitz_ConditionalFiniteSource
public import Definitions.Def_NewtonianLipschitz_TangentialAlgebra
public import Definitions.Def_NewtonianLipschitz_SafePlaneReduction
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
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (x y : Vec3) (d : ℝ) (hd : 0 < d)
    (i : Fin 3)
    (hpos : d ≤ x i) (hneg : y i ≤ -d) :
    d ≤ ‖x - y‖ := by
  have hcomponent :
      |(x - y) i| ≤ ‖x - y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (x - y) i)
  have hdiff : d ≤ x i - y i := by
    linarith
  have heq : (x - y) i = x i - y i := by
    simp
  have habs : d ≤ |(x - y) i| := by
    rw [heq]
    exact hdiff.trans (le_abs_self _)
  exact habs.trans hcomponent
end NewtonianLipschitz
