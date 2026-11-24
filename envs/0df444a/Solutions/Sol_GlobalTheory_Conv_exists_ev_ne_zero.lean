-- Prove2me | solution 1 for GlobalTheory.Conv.exists_ev_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:42:52.167638+00:00
-- url     : https://prove2.me/submissions/5329428c-fcef-4a73-b4d8-0809795bc19a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Theorems.Thm_GlobalTheory_Conv_exists_lsum_eTwoPi_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries LaurentSeries Topology
open Filter
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (eTwoPi SumsAt)
noncomputable section
open GlobalTheory GlobalTheory.Conv
namespace GlobalTheory.Conv
theorem _root_.solution {T : ℝ} {s : halfRing T} (h0 : s ≠ 0) :
    ∃ T' ≥ T, ∀ (w : ℂ) (hw : T < w.im), T' < w.im → ev T w hw s ≠ 0 := by
  have hs0 : (s : ℂ⸨X⸩) ≠ 0 := fun h => h0 (Subtype.ext h)
  obtain ⟨T₁, hT₁⟩ := exists_lsum_eTwoPi_ne_zero (halfRing_le_convLaurent T s.2) hs0
  exact ⟨max T T₁, le_max_left _ _, fun w _ hw' => hT₁ w (lt_of_le_of_lt (le_max_right _ _) hw')⟩
end GlobalTheory.Conv
