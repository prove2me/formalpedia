-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.unitAt_iff_of_valAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:33:31.803514+00:00
-- url     : https://prove2.me/submissions/92ac2732-0920-4a74-9b43-85259c6c29db

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_valAt_inv


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
namespace GlobalTheory.CompanionTheory.Ar.PB
theorem _root_.solution {a : Ω} {r : R} (h : ValAt ξ z a r) (hz : genPt ξ ⤳ centre z) :
    unitAt ξ ⟨centre z, hz⟩ a ↔ r ≠ 0 := by
  constructor
  · obtain ⟨_, s, rfl, rfl⟩ := h
    rintro ⟨h0, -, t, ht⟩ hr
    have hs : ¬ IsUnit s := fun hu => (hu.map (Scheme.stalkClosedPointTo z).hom).ne_zero hr
    have hu : IsUnit (1 - s * t) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun hu => hs (isUnit_of_mul_isUnit_left hu)
    have := hu.map (genMap ξ ⟨centre z, hz⟩)
    rw [map_sub, map_one, map_mul, ht, mul_inv_cancel₀ h0, sub_self] at this
    exact not_isUnit_zero this
  · intro hr
    obtain ⟨h0, _, t, ht, -⟩ := CoordModel.valAt_inv (r := Units.mk0 r hr) h
    obtain ⟨_, s, hs, -⟩ := h
    exact ⟨h0, ⟨s, hs⟩, ⟨t, ht⟩⟩
end GlobalTheory.CompanionTheory.Ar.PB
