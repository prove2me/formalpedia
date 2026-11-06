-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.finiteIndex_range_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:27:43.011207+00:00
-- url     : https://prove2.me/submissions/abcdf2c4-6da7-4132-bd96-8f7accc5ee25

import Mathlib
import Definitions.Def_OAIQ098E007
import Theorems.Thm_OAI_SharpPlanar_Numerical_finiteIndex_bound_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_finiteIndex_cover_check_e

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
lemma finiteIndex_range_e_oai (n : Node) (d : Bool) : (∃ i, finiteIndex i = (n,d)) ↔ n.val ≤ 100 := by
  constructor
  · rintro ⟨i,hi⟩
    have hh := finiteIndex_bound_e i
    simpa only [hi] using hh
  · intro hn
    obtain ⟨i,hin,hid⟩ := finiteIndex_cover_check_e ⟨n.val,Nat.lt_succ_of_le hn⟩ n.prop d
    exact ⟨i,Prod.ext (Subtype.ext hin) hid⟩
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.finiteIndex_range_e_oai := @OAI.SharpPlanar.Numerical.finiteIndex_range_e_oai
