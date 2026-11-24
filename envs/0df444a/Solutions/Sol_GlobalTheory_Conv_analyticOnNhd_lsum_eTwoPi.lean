-- Prove2me | solution 1 for GlobalTheory.Conv.analyticOnNhd_lsum_eTwoPi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:20:53.531326+00:00
-- url     : https://prove2.me/submissions/83f90c97-5a49-4f0f-931f-17c2c8c96a40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Theorems.Thm_GlobalTheory_Conv_differentiable_eTwoPi

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
theorem _root_.solution {T : ℝ} {s : ℂ⸨X⸩} (hs : s ∈ halfRing T) :
    AnalyticOnNhd ℂ (fun w => lsum s (eTwoPi w)) {w : ℂ | T < w.im} := by
  rw [mem_halfRing_iff_puncturedRing] at hs
  intro w hw
  have h1 := analyticOnNhd_lsum hs (eTwoPi w) (eTwoPi_mem_puncturedDisc.2 hw)
  exact h1.comp (differentiable_eTwoPi.analyticAt w)
end GlobalTheory.Conv
