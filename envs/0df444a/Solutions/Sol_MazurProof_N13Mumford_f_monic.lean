-- Prove2me | solution 1 for MazurProof.N13Mumford.f_monic
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:32:17.099675+00:00
-- url     : https://prove2.me/submissions/6a6953d5-4f44-41b3-9362-77ae54715b59

import Mathlib
import Definitions.Def_MazurN13_L0

set_option maxHeartbeats 1000000

-- ===== FLT.Assumptions.MazurProof.N13Mumford =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13Mumford =====
section
/-!
# The smooth sextic and Mumford model for `X₁(13)`

This file instantiates the curve-independent balanced Mumford layer with the
standard sextic model of `X₁(13)`.  Smoothness is proved by a short Bézout
identity between the sextic and its derivative.
-/
open Polynomial
namespace MazurProof.N13Mumford
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
omit [CharZero K] in
theorem f_monic : (f K).Monic := by
  unfold f
  monicity!
/-! ## The six rational cusps -/
end
end MazurProof.N13Mumford
end

end

theorem solution : type_of% @MazurProof.N13Mumford.f_monic := @MazurProof.N13Mumford.f_monic
