-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_6_ii_goalV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T12:15:15.792658+00:00
-- url     : https://prove2.me/submissions/d76d038f-3d64-467f-815f-10ea960b1d16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_6Certification
import Theorems.Thm_Kyprianou_Ch04_exercise46ServiceTrafficRatioV1
import Theorems.Thm_Kyprianou_Ch04_exercise46OverloadedIdleCDFV1
import Theorems.Thm_Kyprianou_Ch04_exercise46ServiceLaplaceBoundsV1
import Theorems.Thm_Kyprianou_Ch04_exercise46BusyStartCountV1
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution : Kyprianou.Ch04.certificate_ex4_6_ii := by
  unfold Kyprianou.Ch04.certificate_ex4_6_ii
  intro Omega m P G L hBV hd lambda hlambda service inst hpos hinput
    Wleft hleft rho hrho hover
  have htraffic := Kyprianou.Ch04.exercise46ServiceTrafficRatioV1
    service hpos lambda hlambda L.ν hinput (by simpa [hrho] using hover)
  obtain ⟨phi, hp, hroot, hmax, hcdf⟩ :=
    Kyprianou.Ch04.exercise46OverloadedIdleCDFV1 P G L hBV hd htraffic
  have hb := Kyprianou.Ch04.exercise46BusyStartCountV1
    P G L hBV hd lambda hlambda service hpos hinput Wleft hleft rho hrho hover
    phi hp hroot hmax
  have hbounds := Kyprianou.Ch04.exercise46ServiceLaplaceBoundsV1 service hpos phi hp
  exact ⟨hb.1, phi, hp, hroot, hmax,
    sub_pos.mpr hbounds.2, by linarith [hbounds.1], hb.2, hcdf⟩
