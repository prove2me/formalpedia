-- Prove2me | solution 1 for GlobalTheory.Conv.exists_lsum_eTwoPi_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:20:56.923798+00:00
-- url     : https://prove2.me/submissions/38615758-ec09-4d4f-b7d3-d533b57ad12f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Theorems.Thm_GlobalTheory_Conv_eventually_iff_eTwoPi
import Theorems.Thm_GlobalTheory_Conv_eventually_lsum_ne_zero


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
theorem _root_.solution {s : ℂ⸨X⸩} (hs : s ∈ convLaurent) (h0 : s ≠ 0) :
    ∃ T : ℝ, ∀ w : ℂ, T < w.im → lsum s (eTwoPi w) ≠ 0 :=
  eventually_iff_eTwoPi.1 (eventually_lsum_ne_zero hs h0)
end GlobalTheory.Conv
