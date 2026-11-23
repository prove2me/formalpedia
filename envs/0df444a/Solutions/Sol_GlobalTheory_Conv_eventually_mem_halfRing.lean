-- Prove2me | solution 1 for GlobalTheory.Conv.eventually_mem_halfRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:32.830839+00:00
-- url     : https://prove2.me/submissions/2b9e6a7a-36d3-4489-be81-f0a20011a276

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Theorems.Thm_GlobalTheory_Conv_mem_convLaurent_iff_halfRing

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
theorem _root_.solution {s : ℂ⸨X⸩} (hs : s ∈ convLaurent) :
    ∀ᶠ T in atTop, s ∈ halfRing T := by
  obtain ⟨T, hT⟩ := mem_convLaurent_iff_halfRing.1 hs
  exact Filter.eventually_atTop.2 ⟨T, fun T' h => halfRing_mono h hT⟩
end GlobalTheory.Conv
