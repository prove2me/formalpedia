-- Prove2me | solution 1 for NewtonianLipschitz.oneSourceGlobalCandidateBound_proved
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:18:08.130181+00:00
-- url     : https://prove2.me/submissions/f689a17a-fc27-410b-a348-88f91a438124

module
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialAllAxes
public import Definitions.Def_NewtonianLipschitz_SafePlaneFiniteDifference
public import Theorems.Thm_NewtonianLipschitz_oneSourceSafePlaneFiveFourthBound_proved
public import Theorems.Thm_NewtonianLipschitz_oneSourceGlobalCandidateBound_of_safePlaneFiveFourth


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution :
    oneSourceGlobalCandidateBound :=
  oneSourceGlobalCandidateBound_of_safePlaneFiveFourth
    oneSourceSafePlaneFiveFourthBound_proved
end NewtonianLipschitz
