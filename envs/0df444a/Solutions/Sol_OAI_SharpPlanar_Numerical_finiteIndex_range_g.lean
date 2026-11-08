-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.finiteIndex_range_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:12:39.318204+00:00
-- url     : https://prove2.me/submissions/722fb3bc-f829-490f-8206-6784cd3152e4

import Mathlib
import Definitions.Def_OAIQ098G007
import Theorems.Thm_OAI_SharpPlanar_Numerical_finiteIndex_bound_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_finiteIndex_cover_check_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Indices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite node coordinates

These coordinates enumerate the value and derivative data on the first
triangular shell nodes in the planar Fourier interpolation problem.
-/

namespace SharpPlanar.Numerical

open scoped BigOperators
lemma finiteIndex_range_g_oai (n : Node) (d : Bool) : (∃ i, finiteIndex i = (n,d)) ↔ n.val ≤ 100 := by
  constructor
  · rintro ⟨i,hi⟩
    have hh := finiteIndex_bound_g i
    simpa only [hi] using hh
  · intro hn
    obtain ⟨i,hin,hid⟩ := finiteIndex_cover_check_g ⟨n.val,Nat.lt_succ_of_le hn⟩ n.prop d
    exact ⟨i,Prod.ext (Subtype.ext hin) hid⟩
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.finiteIndex_range_g_oai := @OAI.SharpPlanar.Numerical.finiteIndex_range_g_oai
