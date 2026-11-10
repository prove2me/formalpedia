-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density0_r5_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:44:21.578048+00:00
-- url     : https://prove2.me/submissions/6d3cfd3e-a7c4-4fb7-a3f4-3efbadceb8b7

import Mathlib
import Definitions.Def_OAIQ098G394
import Definitions.Def_OAIQ098G397
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r5_10_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r5_11_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r5_12_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r5_13_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r5_14_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r5_15_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r5_1_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r5_2_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r5_3_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r5_4_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r5_5_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r5_6_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r5_7_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r5_8_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r5_9_eq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity0Panel5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
lemma density0_r5_0_eq : ∀ k : Fin 16, density0Expr 5 0 k = density0_r5_0 k := by decide +kernel
lemma density0_r5_eq_g_oai (i k : Fin 16) : density0Expr 5 i k = density0_r5 i k := by
  fin_cases i
  · exact density0_r5_0_eq k
  · exact density0_r5_1_eq_g k
  · exact density0_r5_2_eq_g k
  · exact density0_r5_3_eq_g k
  · exact density0_r5_4_eq_g k
  · exact density0_r5_5_eq_g k
  · exact density0_r5_6_eq_g k
  · exact density0_r5_7_eq_g k
  · exact density0_r5_8_eq_g k
  · exact density0_r5_9_eq_g k
  · exact density0_r5_10_eq_g k
  · exact density0_r5_11_eq_g k
  · exact density0_r5_12_eq_g k
  · exact density0_r5_13_eq_g k
  · exact density0_r5_14_eq_g k
  · exact density0_r5_15_eq_g k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density0_r5_eq_g_oai := @OAI.SharpPlanar.CachedData.density0_r5_eq_g_oai
