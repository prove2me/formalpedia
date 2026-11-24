-- Prove2me | solution 1 for GlobalTheory.Conv.differentiableOn_of_eq_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:06:09.253795+00:00
-- url     : https://prove2.me/submissions/76502bc9-4613-49c9-90c3-e16d27fc43a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Theorems.Thm_GlobalTheory_Conv_differentiableOn_lsum_eTwoPi

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
theorem _root_.solution {T : ℝ} (s : halfRing T) {F : ℂ → ℂ}
    (hF : ∀ w (hw : T < w.im), F w = ev T w hw s) : DifferentiableOn ℂ F {w : ℂ | T < w.im} :=
  (differentiableOn_lsum_eTwoPi s.2).congr fun w hw => hF w hw
end GlobalTheory.Conv
