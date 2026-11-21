-- Prove2me | solution 1 for NewtonianLipschitz.oneSourceGlobalCandidateBound_of_safePlaneFiveFourth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:15:55.550185+00:00
-- url     : https://prove2.me/submissions/fee46e72-fe61-4b4c-855a-28f517413749

module
public import Definitions.Def_NewtonianLipschitz_ConditionalFiniteSource
public import Definitions.Def_NewtonianLipschitz_TangentialAlgebra
public import Definitions.Def_NewtonianLipschitz_SafePlaneReduction
public import Theorems.Thm_NewtonianLipschitz_cartesian_exists_signed_safe_coordinate
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_sub_le_candidateMaximum_different_axes_of_safePlane
public import Theorems.Thm_NewtonianLipschitz_cartesian_opposite_safe_sides_separated
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_sub_le_candidateMaximum_common_face
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_sub_le_candidateMaximum_long
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
    (hPlane : oneSourceSafePlaneFiveFourthBound) :
    oneSourceGlobalCandidateBound := by
  intro c x y d hd hx hy
  obtain ⟨i, hxi⟩ := cartesian_exists_signed_safe_coordinate x d hx
  obtain ⟨j, hyj⟩ := cartesian_exists_signed_safe_coordinate y d hy
  by_cases hij : i = j
  · subst j
    rcases hxi with hxpos | hxneg
    · rcases hyj with hypos | hyneg
      · exact c.accelerationField_norm_sub_le_candidateMaximum_common_face
          x y d hd ⟨i, Or.inl ⟨hxpos, hypos⟩⟩
      · have hfar : d ≤ ‖x - y‖ :=
          cartesian_opposite_safe_sides_separated
            x y d hd i hxpos hyneg
        exact c.accelerationField_norm_sub_le_candidateMaximum_long
          x y d hd hx hy hfar
    · rcases hyj with hypos | hyneg
      · have hfar : d ≤ ‖x - y‖ := by
          have hreverse :
              d ≤ ‖y - x‖ :=
            cartesian_opposite_safe_sides_separated
              y x d hd i hypos hxneg
          simpa only [norm_sub_rev] using hreverse
        exact c.accelerationField_norm_sub_le_candidateMaximum_long
          x y d hd hx hy hfar
      · exact c.accelerationField_norm_sub_le_candidateMaximum_common_face
          x y d hd ⟨i, Or.inr ⟨hxneg, hyneg⟩⟩
  · exact c.accelerationField_norm_sub_le_candidateMaximum_different_axes_of_safePlane
      hPlane x y d hd i j hij hxi hyj
end NewtonianLipschitz
