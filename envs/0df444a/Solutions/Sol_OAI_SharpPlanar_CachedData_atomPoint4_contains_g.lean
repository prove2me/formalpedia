-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.atomPoint4_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:36:47.4179+00:00
-- url     : https://prove2.me/submissions/1c58e8c4-ef54-4e6f-8314-ecfa028182ae

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
lemma atomPoint4_contains_g_oai : atomPoint4.Contains (4/6:ℝ) := by
  have ht : atomPoint4.t.Contains (4/6:ℝ) := by
    convert RBox.contains_rat_g 4 6 (by norm_num) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [atomPoint4]
    decide +kernel
  have he : PointBox.calc atomPoint4.t = atomPoint4 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.atomPoint4_contains_g_oai := @OAI.SharpPlanar.CachedData.atomPoint4_contains_g_oai
