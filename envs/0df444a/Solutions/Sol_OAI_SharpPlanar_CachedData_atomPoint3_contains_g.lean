-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.atomPoint3_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:36:15.087471+00:00
-- url     : https://prove2.me/submissions/851e4b27-3591-49f3-9dc6-26753d43775b

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
lemma atomPoint3_contains_g_oai : atomPoint3.Contains (3/6:ℝ) := by
  have ht : atomPoint3.t.Contains (3/6:ℝ) := by
    convert RBox.contains_rat_g 3 6 (by norm_num) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [atomPoint3]
    decide +kernel
  have he : PointBox.calc atomPoint3.t = atomPoint3 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.atomPoint3_contains_g_oai := @OAI.SharpPlanar.CachedData.atomPoint3_contains_g_oai
