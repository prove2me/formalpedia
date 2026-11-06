-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.atomPoint5_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T04:53:14.57148+00:00
-- url     : https://prove2.me/submissions/e08c26e7-1aa4-41e4-9931-b82c07e1fb62

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
lemma atomPoint5_contains_e_oai : atomPoint5.Contains (5/6:ℝ) := by
  have ht : atomPoint5.t.Contains (5/6:ℝ) := by
    convert RBox.contains_rat_e 5 6 (by norm_num) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [atomPoint5]
    decide +kernel
  have he : PointBox.calc atomPoint5.t = atomPoint5 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_e ht (by decide +kernel)
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.atomPoint5_contains_e_oai := @OAI.SharpPlanar.CachedData.atomPoint5_contains_e_oai
