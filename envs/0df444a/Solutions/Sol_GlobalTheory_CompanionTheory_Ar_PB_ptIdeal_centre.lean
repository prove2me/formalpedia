-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.ptIdeal_centre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:03:52.311474+00:00
-- url     : https://prove2.me/submissions/e7b4ef10-6fa7-4bfd-99a2-8d7c939efc5a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_unitAt_iff_of_valAt
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_inBlockChart_centre_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_valAt_form
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_form_mem_mCoordIdeal_iff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_isMultiHomogIdeal_e52032a6c383


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
theorem _root_.solution (hw : CoordsAt ξ x z w) (hz : genPt ξ ⤳ centre z) :
    ptIdeal ξ x ⟨centre z, hz⟩ = mCoordIdeal w := by
  have key : ∀ (g : MRing J) (d : K → ℕ), IsMultiHomog g d → ∀ c, InBlockChart ξ x c ⟨centre z, hz⟩ →
      (¬ unitAt ξ ⟨centre z, hz⟩ (MvPolynomial.aeval x g / ∏ k, x ⟨k, c k⟩ ^ d k) ↔ g ∈ mCoordIdeal w) := by
    intro g d hg c hc
    have hc' := (inBlockChart_centre_iff hw hz c).1 hc
    have h0 : (∏ k, w ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc' k)
    rw [unitAt_iff_of_valAt (valAt_form hw hz hc' hg) hz, form_mem_mCoordIdeal_iff w hg, not_not, div_eq_zero_iff,
      or_iff_left h0]
  refine le_antisymm (Ideal.span_le.2 ?_) ?_
  · rintro g ⟨d, hg, h⟩
    choose c hc using hw.1
    have hc' := (inBlockChart_centre_iff hw hz c).2 fun k => (hc k).ne_zero
    exact (key g d hg c hc').1 (h c hc')
  · obtain ⟨T, hT, e⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal w
    refine e.le.trans (Ideal.span_mono fun g hg => ?_)
    obtain ⟨d, hd⟩ := hT g hg
    exact ⟨d, hd, fun c hc => (key g d hd c hc).2 (e ▸ Ideal.subset_span hg)⟩
end GlobalTheory.CompanionTheory.Ar.PB
