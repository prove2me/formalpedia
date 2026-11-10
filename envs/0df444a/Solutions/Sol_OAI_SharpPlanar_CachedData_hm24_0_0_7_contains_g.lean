-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.hm24_0_0_7.contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:59:06.536575+00:00
-- url     : https://prove2.me/submissions/1a944862-cd0d-46d9-ad23-5470ad2f41cd

import Mathlib
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G1018
import Definitions.Def_OAIQ098G1044
import Definitions.Def_OAIQ098G1682
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hk24_0_7_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm24_0_0_7_sums_eq_g
import Theorems.Thm_OAI_SharpPlanar_cached_density_rule_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock24_0
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
namespace hm24_0_0_7
lemma checked : cachedMomentRuleBox density0 hk24_0_7 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq_g]
  decide +kernel
lemma contains_g_oai : ans.Contains (fullMomentRule false false 24 7) := by
  rw [← checked]
  exact @cached_density_rule_contains_g density0 hk24_0_7 (tableDensity false) (fullFactor false 24 7) density0_contains_g hk24_0_7_contains_g
end hm24_0_0_7
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.hm24_0_0_7.contains_g_oai := @OAI.SharpPlanar.CachedData.hm24_0_0_7.contains_g_oai
