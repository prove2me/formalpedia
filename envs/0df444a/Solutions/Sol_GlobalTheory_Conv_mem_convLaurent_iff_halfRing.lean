-- Prove2me | solution 1 for GlobalTheory.Conv.mem_convLaurent_iff_halfRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:19.018598+00:00
-- url     : https://prove2.me/submissions/8387a19d-a88b-40e3-9bcc-14bd2388c727

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Theorems.Thm_GlobalTheory_Conv_exists_cuspRadius_eq

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
theorem _root_.solution {s : ℂ⸨X⸩} : s ∈ convLaurent ↔ ∃ T, s ∈ halfRing T := by
  rw [mem_convLaurent]
  constructor
  · rintro ⟨ε, hε, h⟩
    obtain ⟨T, rfl⟩ := exists_cuspRadius_eq hε
    exact ⟨T, mem_halfRing_iff_puncturedRing.2 h⟩
  · rintro ⟨T, h⟩
    exact ⟨_, cuspRadius_pos T, mem_halfRing_iff_puncturedRing.1 h⟩
end GlobalTheory.Conv
