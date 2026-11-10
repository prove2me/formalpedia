-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density1_r0_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:48:12.252756+00:00
-- url     : https://prove2.me/submissions/cd3387aa-7891-4414-ae47-76c869701024

import Mathlib
import Definitions.Def_OAIQ098G397
import Definitions.Def_OAIQ098G399
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r0_0_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r0_10_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r0_11_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r0_12_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r0_13_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r0_14_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r0_1_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r0_2_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r0_3_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r0_4_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r0_5_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r0_6_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r0_7_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r0_8_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r0_9_eq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity1Panel0
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
lemma density1_r0_15_eq : ∀ k : Fin 16, density1Expr 0 15 k = density1_r0_15 k := by decide +kernel
lemma density1_r0_eq_g_oai (i k : Fin 16) : density1Expr 0 i k = density1_r0 i k := by
  fin_cases i
  · exact density1_r0_0_eq_g k
  · exact density1_r0_1_eq_g k
  · exact density1_r0_2_eq_g k
  · exact density1_r0_3_eq_g k
  · exact density1_r0_4_eq_g k
  · exact density1_r0_5_eq_g k
  · exact density1_r0_6_eq_g k
  · exact density1_r0_7_eq_g k
  · exact density1_r0_8_eq_g k
  · exact density1_r0_9_eq_g k
  · exact density1_r0_10_eq_g k
  · exact density1_r0_11_eq_g k
  · exact density1_r0_12_eq_g k
  · exact density1_r0_13_eq_g k
  · exact density1_r0_14_eq_g k
  · exact density1_r0_15_eq k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density1_r0_eq_g_oai := @OAI.SharpPlanar.CachedData.density1_r0_eq_g_oai
