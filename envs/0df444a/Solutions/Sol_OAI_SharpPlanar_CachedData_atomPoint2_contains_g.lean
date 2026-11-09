-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.atomPoint2_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:36:12.229144+00:00
-- url     : https://prove2.me/submissions/b514f4be-dd0e-4a1e-aeb6-df6ad5a4c371

import Mathlib
import Definitions.Def_OAIQ098G090
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G093
import Definitions.Def_OAIQ098G383
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_PointBox_calc_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_AtomKernels
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
lemma atomPoint2_contains_g_oai : atomPoint2.Contains (2/6:ℝ) := by
  have ht : atomPoint2.t.Contains (2/6:ℝ) := by
    convert RBox.contains_rat_g 2 6 (by norm_num) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [atomPoint2]
    decide +kernel
  have he : PointBox.calc atomPoint2.t = atomPoint2 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.atomPoint2_contains_g_oai := @OAI.SharpPlanar.CachedData.atomPoint2_contains_g_oai
