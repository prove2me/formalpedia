-- Prove2me | solution 1 for MazurProof.N13Infinity.reverseTail_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:31:36.37759+00:00
-- url     : https://prove2.me/submissions/06913846-10e9-4df0-85b9-93579866e985

import Mathlib
import Definitions.Def_MazurN13_L0

set_option maxHeartbeats 1000000

-- ===== FLT.Assumptions.MazurProof.N13Infinity =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13Infinity =====
section
/-!
# The positive infinity of the N13 genus-two curve

We construct the chosen branch at infinity inside `K((s))`.  With `x=s⁻¹`,
the equation becomes

`(s³ y)² = 1 + 4s + 6s² + 2s³ + s⁴ + 2s⁵ + s⁶`.

The square root with constant coefficient `+1` is obtained from the formal
binomial series.  The resulting embedding of the function field supplies the
integer orientation used in `SexticMumford`.
-/
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13Infinity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
/-! ## The formal positive square root -/
omit [CharZero K] in
@[simp] theorem reverseTail_constantCoeff :
    PowerSeries.constantCoeff (reverseTail K) = 0 := by
  simp [reverseTail, reverseF]
/-! ## An algebraic model of the function field -/
/-! ## The branch `x = s⁻¹`, `s³y = +sqrt(reverseF)` -/
end
end MazurProof.N13Infinity
end

end

theorem solution : type_of% @MazurProof.N13Infinity.reverseTail_constantCoeff := @MazurProof.N13Infinity.reverseTail_constantCoeff
