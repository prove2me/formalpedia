-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.inBlockChart_centre_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:53:43.464325+00:00
-- url     : https://prove2.me/submissions/78a5b84e-98ff-425b-aa57-a1c19565c02b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_unitAt_iff_of_valAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {Z : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
variable {ξ : Spec (CommRingCat.of Ω) ⟶ Z} {x : (Σ k, J k) → Ω} {R : Type} [Field R]
  {z : Spec (CommRingCat.of R) ⟶ Z} {w : (Σ k, J k) → R}
omit [Fintype K] [∀ k, Fintype (J k)]
namespace GlobalTheory.CompanionTheory.Ar.PB
theorem _root_.solution (hw : CoordsAt ξ x z w) (hz : genPt ξ ⤳ centre z) (c : ∀ k, J k) :
    InBlockChart ξ x c ⟨centre z, hz⟩ ↔ ∀ k, w ⟨k, c k⟩ ≠ 0 := by
  refine forall_congr' fun k => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨d, hd⟩ := hw.1 k
    obtain ⟨hd0, hv⟩ := hw.2 k d hd
    obtain ⟨r, hr, e⟩ := hv (c k)
    have hu : unitAt ξ ⟨centre z, hz⟩ (x ⟨k, c k⟩ / x ⟨k, d⟩) := by
      obtain ⟨_, s, hs, -⟩ := hr
      refine ⟨div_ne_zero h.1 hd0, ⟨s, hs⟩, ?_⟩
      rw [inv_div]
      exact h.2 d
    rw [e]
    exact mul_ne_zero ((unitAt_iff_of_valAt hr hz).1 hu) hd.ne_zero
  · obtain ⟨h0, hv⟩ := hw.2 k (c k) (IsUnit.mk0 _ h)
    refine ⟨h0, fun i => ?_⟩
    obtain ⟨r, ⟨_, s, hs, -⟩, -⟩ := hv i
    exact ⟨s, hs⟩
end GlobalTheory.CompanionTheory.Ar.PB
