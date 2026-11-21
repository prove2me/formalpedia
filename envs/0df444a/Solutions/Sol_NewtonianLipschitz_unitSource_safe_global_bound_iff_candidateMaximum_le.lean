-- Prove2me | solution 1 for NewtonianLipschitz.unitSource_safe_global_bound_iff_candidateMaximum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:22:59.342479+00:00
-- url     : https://prove2.me/submissions/05634f29-be3a-48b9-8505-9d2a6cf8a20b

module
public import Definitions.Def_NewtonianLipschitz_SafePlaneFiniteDifference
public import Definitions.Def_NewtonianLipschitz_UnconditionalFiniteSource
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_cons
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_nil
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_gravitationalParameter_eq_one
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_le_of_universal_safe_secant_bound
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
public import Theorems.Thm_NewtonianLipschitz_oneSourceGlobalCandidateBound_proved
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
    (K : ℝ) :
    (∀ x y : Vec3,
      (1 : ℝ) ≤ ‖x‖ →
      (1 : ℝ) ≤ ‖y‖ →
      ‖NewtonianPointSource.unitAxis.accelerationField x -
        NewtonianPointSource.unitAxis.accelerationField y‖ ≤
          K * ‖x - y‖) ↔ candidateMaximum ≤ K := by
  constructor
  · exact candidateMaximum_le_of_universal_safe_secant_bound K
  · intro hCK x y hx hy
    have hglobal :=
      oneSourceGlobalCandidateBound_proved
        NewtonianPointSource.unitAxis x y 1
        (by norm_num) hx hy
    have hsharp :
        ‖NewtonianPointSource.unitAxis.accelerationField x -
          NewtonianPointSource.unitAxis.accelerationField y‖ ≤
            candidateMaximum * ‖x - y‖ := by
      simpa only [NewtonianPointSource.unitAxis_gravitationalParameter_eq_one,
        one_pow, div_one, one_mul] using hglobal
    exact hsharp.trans
      (mul_le_mul_of_nonneg_right hCK (norm_nonneg _))
end NewtonianLipschitz
