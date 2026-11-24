-- Prove2me | solution 1 for GlobalTheory.Conv.locRing_toSubring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:00:08.506953+00:00
-- url     : https://prove2.me/submissions/c3be699f-3b9e-4b5c-9718-c2b4b6f806d1

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
theorem _root_.solution {T : ℝ} (s : halfRing T) :
    (locRing T s).toSubring = Subring.closure ((halfRing T : Set ℂ⸨X⸩) ∪ {(s : ℂ⸨X⸩)⁻¹}) := by
  have hr : Set.range (algebraMap (halfRing T) ℂ⸨X⸩) = (halfRing T : Set ℂ⸨X⸩) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [locRing, Algebra.adjoin_eq_ring_closure, hr]
end GlobalTheory.Conv
