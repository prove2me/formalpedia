-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_exercise8_2_i_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:41:07.224932+00:00
-- url     : https://prove2.me/submissions/b6244bbb-4bcc-46ab-a674-c2f1b28ce8b8

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_stable_integrated_coeff_summable
import Theorems.Thm_Kyprianou_Ch08_StageB_source_stable_integrated_scale_laplace
import Theorems.Thm_Kyprianou_Ch08_StageB_source_stable_integrated_series_closedform
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution : exercise8_2_i := by
  intro α q β W hα hα2 hq hβ hW
  exact ⟨source_stable_integrated_coeff_summable α q β hα hq hβ,
    source_stable_integrated_scale_laplace α q β W hα hq hβ hW,
    source_stable_integrated_series_closedform α q β hα hq hβ⟩
