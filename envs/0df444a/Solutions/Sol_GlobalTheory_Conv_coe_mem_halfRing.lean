-- Prove2me | solution 1 for GlobalTheory.Conv.coe_mem_halfRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:45:05.497188+00:00
-- url     : https://prove2.me/submissions/844a2061-42df-407d-b114-0b78a0e2b68c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi

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
theorem _root_.solution {T : ℝ} {p : ℂ⟦X⟧} :
    (p : ℂ⸨X⸩) ∈ halfRing T ↔ ∀ w : ℂ, T < w.im → ∃ x, SumsAt p w x := by
  rw [mem_halfRing]
  refine forall₂_congr fun w _ => ⟨fun h => ⟨_, hasSum_coe_iff.1 h.hasSum⟩, ?_⟩
  rintro ⟨x, hx⟩
  exact (hasSum_coe_iff.2 hx).summable
end GlobalTheory.Conv
