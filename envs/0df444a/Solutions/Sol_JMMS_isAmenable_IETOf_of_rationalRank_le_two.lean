-- Prove2me | solution 1 for JMMS.isAmenable_IETOf_of_rationalRank_le_two
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T10:57:49.352646+00:00
-- url     : https://prove2.me/submissions/6154c30d-c79b-4d57-85cb-76550b6d32c8

import Mathlib
import Definitions.Def_IntervalExchange
import Theorems.Thm_JMMS_isRecurrentAction_and_isExtensivelyAmenable_IETOf
import Theorems.Thm_JMMS_isAmenable_iff_isExtensivelyAmenable_of_le_IET

section
open IntervalExchange

namespace JMMS

theorem chk_isAmenable_IETOf_of_rationalRank_le_two (Λ : AddSubgroup UnitAddCircle) (hΛ : Λ.FG)
    (hrk : rationalRank Λ ≤ 2) : Garrido.IsAmenable ↥(IETOf Λ) := by
  exact (isAmenable_iff_isExtensivelyAmenable_of_le_IET (IETOf Λ) inf_le_left).2
    (isRecurrentAction_and_isExtensivelyAmenable_IETOf Λ hΛ hrk).2

end JMMS
end

open IntervalExchange
open JMMS in
theorem solution (Λ : AddSubgroup UnitAddCircle) (hΛ : Λ.FG)
    (hrk : rationalRank Λ ≤ 2) : Garrido.IsAmenable ↥(IETOf Λ) := by
  apply JMMS.chk_isAmenable_IETOf_of_rationalRank_le_two <;> assumption
