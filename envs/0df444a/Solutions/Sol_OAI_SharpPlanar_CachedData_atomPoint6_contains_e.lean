-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.atomPoint6_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T04:53:36.504827+00:00
-- url     : https://prove2.me/submissions/bc41b1cd-9e31-467d-b6b9-632f2aaa26b9

import Mathlib
import Definitions.Def_OAIQ098E130
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_PointBox_calc_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_e

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
lemma atomPoint6_contains_e_oai : atomPoint6.Contains (6/6:ℝ) := by
  have ht : atomPoint6.t.Contains (6/6:ℝ) := by
    convert RBox.contains_rat_e 6 6 (by norm_num) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [atomPoint6]
    decide +kernel
  have he : PointBox.calc atomPoint6.t = atomPoint6 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_e ht (by decide +kernel)
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.atomPoint6_contains_e_oai := @OAI.SharpPlanar.CachedData.atomPoint6_contains_e_oai
