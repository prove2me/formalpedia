-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.valAt_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:45:19.749876+00:00
-- url     : https://prove2.me/submissions/2463d781-d059-4886-9f20-d5907ed41bd0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_valAt_aeval
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_aeval_blockScale


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
theorem _root_.solution (hw : CoordsAt ξ x z w) (hz : genPt ξ ⤳ centre z) {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0)
    {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    ValAt ξ z (MvPolynomial.aeval x g / ∏ k, x ⟨k, c k⟩ ^ d k) (MvPolynomial.aeval w g / ∏ k, w ⟨k, c k⟩ ^ d k) := by
  have hy := fun k => (hw.2 k (c k) (IsUnit.mk0 _ (hc k))).1
  choose r hr hr' using fun p : Σ k, J k => (hw.2 p.1 (c p.1) (IsUnit.mk0 _ (hc p.1))).2 p.2
  convert valAt_aeval hz hr g using 1
  · have e : x = fun p => x ⟨p.1, c p.1⟩ * (x ⟨p.1, p.2⟩ / x ⟨p.1, c p.1⟩) :=
      funext fun p => (mul_div_cancel₀ _ (hy p.1)).symm
    have e' := aeval_blockScale hg (fun k => x ⟨k, c k⟩) fun p => x ⟨p.1, p.2⟩ / x ⟨p.1, c p.1⟩
    rw [← e] at e'
    have h0 : (∏ k, x ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
    rw [e']
    field_simp
  · have e : w = fun p => w ⟨p.1, c p.1⟩ * r p := funext fun p => (hr' p).trans (mul_comm _ _)
    have e' := aeval_blockScale hg (fun k => w ⟨k, c k⟩) r
    rw [← e] at e'
    have h0 : (∏ k, w ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
    rw [e']
    field_simp
end GlobalTheory.CompanionTheory.Ar.PB
