-- Prove2me | solution 1 for GlobalTheory.isAEOrbitSection_sign_Ici
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:41:21.420467+00:00
-- url     : https://prove2.me/submissions/19002f7f-ad7a-4f07-bbcc-0ea41e6e204d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology Filter
open scoped Pointwise ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : IsAEOrbitSection ℤˣ (Ici (0 : ℝ)) volume where
  nullMeasurableSet := measurableSet_Ici.nullMeasurableSet
  ae_covers := Eventually.of_forall fun x => by
    rcases le_total 0 x with h | h
    · exact ⟨1, by simpa using h⟩
    · exact ⟨-1, by simpa using h⟩
  ae_unique := Eventually.of_forall fun x hx g hg => by
    rcases Int.units_eq_one_or g with rfl | rfl
    · simp
    · have h1 : x ≤ 0 := by simpa using hg
      have : x = 0 := le_antisymm h1 hx
      simp [this]
end GlobalTheory
