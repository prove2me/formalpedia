-- Prove2me | solution 1 for GlobalTheory.Conv.eq_zero_of_ev_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:06:18.206636+00:00
-- url     : https://prove2.me/submissions/c5edf074-7e85-4ec9-9eca-d60464023f3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Theorems.Thm_GlobalTheory_Conv_exists_ev_ne_zero

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
theorem _root_.solution {T : ℝ} {s : halfRing T} (T' : ℝ)
    (h : ∀ (w : ℂ) (hw : T < w.im), T' < w.im → ev T w hw s = 0) : s = 0 := by
  by_contra h0
  obtain ⟨T'', hT'', h1⟩ := exists_ev_ne_zero h0
  let w : ℂ := ⟨0, max T'' T' + 1⟩
  have hwT : T < w.im := by
    show T < max T'' T' + 1
    linarith [le_max_left T'' T']
  have hw1 : T'' < w.im := by
    show T'' < max T'' T' + 1
    linarith [le_max_left T'' T']
  have hw2 : T' < w.im := by
    show T' < max T'' T' + 1
    linarith [le_max_right T'' T']
  exact h1 w hwT hw1 (h w hwT hw2)
end GlobalTheory.Conv
