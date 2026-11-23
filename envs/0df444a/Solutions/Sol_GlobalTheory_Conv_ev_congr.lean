-- Prove2me | solution 1 for GlobalTheory.Conv.ev_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:21:27.662276+00:00
-- url     : https://prove2.me/submissions/e9bc6bcb-0c34-4f3f-b5a9-6890f4ff5b19

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
theorem _root_.solution {T T' : ℝ} {w : ℂ} (hw : T < w.im) (hw' : T' < w.im) {s : halfRing T}
    {s' : halfRing T'} (h : (s : ℂ⸨X⸩) = s') : ev T w hw s = ev T' w hw' s' := by
  rw [ev_apply, ev_apply, h]
end GlobalTheory.Conv
