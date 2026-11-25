-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.RegAt.mem_regAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:33:39.481935+00:00
-- url     : https://prove2.me/submissions/517b1776-d169-46ab-874c-88b7d979c268

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_unitAt_iff_of_valAt
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_valAt_form
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_form_mem_mCoordIdeal_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_ptIdeal_centre
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_exists_ptIdeal_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


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
namespace RegAt
theorem _root_.solution (h : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) {q : Cpt ξ} {s : Ω}
    (hs : RegAt x (ptIdeal ξ x q) s) : s ∈ regAt ξ q := by
  obtain ⟨R, _, z, w, e, hw, -⟩ := exists_ptIdeal_eq h q
  have hz : genPt ξ ⤳ centre z := e ▸ q.2
  obtain rfl : q = ⟨centre z, hz⟩ := Subtype.ext e.symm
  obtain ⟨d, g, t, hg, ht, htQ, e'⟩ := hs
  rw [ptIdeal_centre hw hz, form_mem_mCoordIdeal_iff w ht] at htQ
  choose c hc using hw.1
  have hc' : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have h0 : (∏ k, w ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc' k)
  obtain ⟨h1, -, h2⟩ := (unitAt_iff_of_valAt (valAt_form hw hz hc' ht) hz).2 (div_ne_zero htQ h0)
  obtain ⟨_, u, hu, -⟩ := valAt_form hw hz hc' hg
  have h3 := (regAt ξ ⟨centre z, hz⟩).mul_mem ⟨u, hu⟩ h2
  rwa [e', mul_div_assoc, mul_assoc, mul_inv_cancel₀ h1, mul_one] at h3
end RegAt
end GlobalTheory.CompanionTheory.Ar.PB
