-- Prove2me | solution 1 for GlobalTheory.Conv.evLoc_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:57:15.556156+00:00
-- url     : https://prove2.me/submissions/a1eeda0d-d461-4f1c-b362-99924f209681

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Theorems.Thm_GlobalTheory_Conv_evLoc_algebraMap
import Theorems.Thm_GlobalTheory_Conv_coe_expandConv
import Theorems.Thm_GlobalTheory_Conv_coe_expandConvLaurent
import Theorems.Thm_GlobalTheory_Conv_expandConv_u
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Conv.coe_expandConv
attribute [local simp] GlobalTheory.Conv.coe_expandConvLaurent
attribute [local simp] GlobalTheory.Conv.expandConv_u


attribute [local simp] GlobalTheory.Conv.evLoc_algebraMap

set_option autoImplicit false
open scoped PowerSeries LaurentSeries Topology
open Filter
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (eTwoPi SumsAt)
noncomputable section
open GlobalTheory GlobalTheory.Conv
namespace GlobalTheory.Conv
theorem _root_.solution {T : ℝ} {w : ℂ} (hw : T < w.im) {s : halfRing T}
    (hs : ev T w hw s ≠ 0) (φ : locRing T s →+* ℂ)
    (hφ : ∀ f, φ (algebraMap _ _ f) = ev T w hw f) (x : locRing T s) :
    φ x = evLoc T w hw s hs x := by
  have h0 : s ≠ 0 := fun h => hs (by rw [h, map_zero])
  have := isLocalization_locRing h0
  have key : φ = (evLoc T w hw s hs : locRing T s →+* ℂ) :=
    IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun f => by simp [hφ])
  exact RingHom.congr_fun key x
end GlobalTheory.Conv
