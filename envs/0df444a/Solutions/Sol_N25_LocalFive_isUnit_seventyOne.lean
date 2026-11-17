-- Prove2me | solution 1 for N25.LocalFive.isUnit_seventyOne
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:24.387881+00:00
-- url     : https://prove2.me/submissions/e8bafb87-12e5-49aa-9ef1-40bc968dd087

import Mathlib
import Definitions.Def_N25_LocalFiveArithmetic

noncomputable section

local instance instL_N25_LocalFive_isUnit_seventyOne_bfd51b_s99d4d7 : Fact (Nat.Prime 5) := ⟨by decide⟩

namespace N25.LocalFive

/-- The scalar 71 is a unit in the 5-adic integers. -/
theorem _root_.solution : IsUnit (71 : R5) := by
  apply PadicInt.isUnit_iff.mpr
  exact PadicInt.norm_natCast_eq_one_iff.mpr (by decide : Nat.Coprime 5 71)

end N25.LocalFive
