-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density1_r5_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:59:33.992872+00:00
-- url     : https://prove2.me/submissions/dec5a2f8-9976-4283-bd31-9161a25b6d89

import Mathlib
import Definitions.Def_OAIQ098G397
import Definitions.Def_OAIQ098G409
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r5_10_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r5_11_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r5_12_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r5_13_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r5_14_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r5_15_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r5_1_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r5_2_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r5_3_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r5_4_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r5_5_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r5_6_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r5_7_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r5_8_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r5_9_eq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity1Panel5
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
lemma density1_r5_0_eq : ∀ k : Fin 16, density1Expr 5 0 k = density1_r5_0 k := by decide +kernel
lemma density1_r5_eq_g_oai (i k : Fin 16) : density1Expr 5 i k = density1_r5 i k := by
  fin_cases i
  · exact density1_r5_0_eq k
  · exact density1_r5_1_eq_g k
  · exact density1_r5_2_eq_g k
  · exact density1_r5_3_eq_g k
  · exact density1_r5_4_eq_g k
  · exact density1_r5_5_eq_g k
  · exact density1_r5_6_eq_g k
  · exact density1_r5_7_eq_g k
  · exact density1_r5_8_eq_g k
  · exact density1_r5_9_eq_g k
  · exact density1_r5_10_eq_g k
  · exact density1_r5_11_eq_g k
  · exact density1_r5_12_eq_g k
  · exact density1_r5_13_eq_g k
  · exact density1_r5_14_eq_g k
  · exact density1_r5_15_eq_g k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density1_r5_eq_g_oai := @OAI.SharpPlanar.CachedData.density1_r5_eq_g_oai
