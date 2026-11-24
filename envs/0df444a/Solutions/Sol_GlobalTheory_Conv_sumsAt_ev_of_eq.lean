-- Prove2me | solution 1 for GlobalTheory.Conv.sumsAt_ev_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:52.806492+00:00
-- url     : https://prove2.me/submissions/fd815f8c-6f32-4d5d-a595-268aa39ef1e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Theorems.Thm_GlobalTheory_Conv_ev_congr
import Theorems.Thm_GlobalTheory_Conv_sumsAt_ev

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
theorem _root_.solution {T : ℝ} {w : ℂ} (hw : T < w.im) {p : ℂ⟦X⟧} {s : halfRing T}
    (h : (p : ℂ⸨X⸩) = s) : SumsAt p w (ev T w hw s) := by
  have hp : (p : ℂ⸨X⸩) ∈ halfRing T := h ▸ s.2
  rw [ev_congr hw hw (s' := (⟨p, hp⟩ : halfRing T)) h.symm]
  exact sumsAt_ev hw hp
end GlobalTheory.Conv
