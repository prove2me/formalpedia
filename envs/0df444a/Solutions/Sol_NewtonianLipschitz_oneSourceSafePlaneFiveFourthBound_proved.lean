-- Prove2me | solution 1 for NewtonianLipschitz.oneSourceSafePlaneFiveFourthBound_proved
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:13:12.93089+00:00
-- url     : https://prove2.me/submissions/6970cc67-fcdf-4197-bc54-73fd1f17ecc0

module
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialAllAxes
public import Definitions.Def_NewtonianLipschitz_SafePlaneFiniteDifference
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_sub_le_fiveFourth_safePlane

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution :
    oneSourceSafePlaneFiveFourthBound := by
  intro c x y d i hd hxy hsafe
  exact c.accelerationField_norm_sub_le_fiveFourth_safePlane
    x y d i hd hxy hsafe
end NewtonianLipschitz
