-- Prove2me | solution 1 for GlobalTheory.Conv.exists_forall_mem_halfRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:11.251217+00:00
-- url     : https://prove2.me/submissions/295ebe9f-1bc0-4fe9-a50a-11317a8bfbdc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Theorems.Thm_GlobalTheory_Conv_eventually_mem_halfRing

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
theorem _root_.solution {S : Set ℂ⸨X⸩} (hS : S.Finite)
    (h : ∀ s ∈ S, s ∈ convLaurent) : ∃ T, ∀ s ∈ S, s ∈ halfRing T :=
  ((Filter.eventually_all_finite hS).2 fun s hs => eventually_mem_halfRing (h s hs)).exists
end GlobalTheory.Conv
