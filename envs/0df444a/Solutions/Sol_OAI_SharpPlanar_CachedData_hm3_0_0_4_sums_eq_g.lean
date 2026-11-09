-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.hm3_0_0_4.sums_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:03:51.947371+00:00
-- url     : https://prove2.me/submissions/d875a39a-cd10-4798-8456-a4bc3c7e36d7

import Mathlib
import Definitions.Def_OAIQ098G1209
import Definitions.Def_OAIQ098G1219
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm3_0_0_4_s1_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm3_0_0_4_s2_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm3_0_0_4_s3_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm3_0_0_4_s4_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm3_0_0_4_s5_eq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments3_0
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
namespace hm3_0_0_4
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
lemma sums_eq_g_oai (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq_g i
  · exact s2_eq_g i
  · exact s3_eq_g i
  · exact s4_eq_g i
  · exact s5_eq_g i
end hm3_0_0_4
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.hm3_0_0_4.sums_eq_g_oai := @OAI.SharpPlanar.CachedData.hm3_0_0_4.sums_eq_g_oai
