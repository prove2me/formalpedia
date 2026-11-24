-- Prove2me | solution 1 for GlobalTheory.Conv.exists_inv_mem_halfRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:57:19.386817+00:00
-- url     : https://prove2.me/submissions/0ec4a2a1-01fc-49a2-9a01-08949f362302

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
theorem _root_.solution {T : ℝ} (s : halfRing T) :
    ∃ T' ≥ T, (s : ℂ⸨X⸩)⁻¹ ∈ halfRing T' := by
  have h1 : ((s : ℂ⸨X⸩))⁻¹ ∈ convLaurent := convLaurent.inv_mem (halfRing_le_convLaurent T s.2)
  obtain ⟨T', hT'⟩ := ((eventually_mem_halfRing h1).and (eventually_ge_atTop T)).exists
  exact ⟨T', hT'.2, hT'.1⟩
end GlobalTheory.Conv
