-- Prove2me | solution 1 for GlobalTheory.Conv.sumsAt_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:25:08.374205+00:00
-- url     : https://prove2.me/submissions/25f5b4e0-2b1e-4dab-8d98-d8da0cf513cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Theorems.Thm_GlobalTheory_Conv_hasSum_ev

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
theorem _root_.solution {T : ℝ} {w : ℂ} (hw : T < w.im) {p : ℂ⟦X⟧} (hp : (p : ℂ⸨X⸩) ∈ halfRing T) :
    SumsAt p w (ev T w hw ⟨p, hp⟩) := hasSum_coe_iff.1 (hasSum_ev hw ⟨p, hp⟩)
end GlobalTheory.Conv
