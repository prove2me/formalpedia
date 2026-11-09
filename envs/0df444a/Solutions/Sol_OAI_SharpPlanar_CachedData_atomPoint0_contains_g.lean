-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.atomPoint0_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:35:41.428711+00:00
-- url     : https://prove2.me/submissions/553943f5-6e3d-4b82-b08d-682f79d46f27

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
lemma atomPoint0_contains_g_oai : atomPoint0.Contains (0/6:ℝ) := by
  have ht : atomPoint0.t.Contains (0/6:ℝ) := by
    convert RBox.contains_rat_g 0 6 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [atomPoint0])
    decide +kernel
  have he : PointBox.calc atomPoint0.t = atomPoint0 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.atomPoint0_contains_g_oai := @OAI.SharpPlanar.CachedData.atomPoint0_contains_g_oai
