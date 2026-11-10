-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.hm33_0_0_5.contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T01:23:28.169337+00:00
-- url     : https://prove2.me/submissions/abc685eb-1bf6-4a5d-a824-a197c794245b

import Mathlib
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G1143
import Definitions.Def_OAIQ098G1151
import Definitions.Def_OAIQ098G1682
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hk33_0_5_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm33_0_0_5_sums_eq_g
import Theorems.Thm_OAI_SharpPlanar_cached_density_rule_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock33_0
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm33_0_0_5
lemma checked : cachedMomentRuleBox density0 hk33_0_5 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq_g]
  decide +kernel
lemma contains_g_oai : ans.Contains (fullMomentRule false false 33 5) := by
  rw [← checked]
  exact @cached_density_rule_contains_g density0 hk33_0_5 (tableDensity false) (fullFactor false 33 5) density0_contains_g hk33_0_5_contains_g
end hm33_0_0_5
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.hm33_0_0_5.contains_g_oai := @OAI.SharpPlanar.CachedData.hm33_0_0_5.contains_g_oai
