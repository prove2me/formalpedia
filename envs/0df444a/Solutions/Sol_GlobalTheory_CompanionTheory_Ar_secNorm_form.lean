-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.secNorm_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:33:54.541392+00:00
-- url     : https://prove2.me/submissions/62854c4d-8904-4d80-8911-b7710cce2bf3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_HodgeIPIffHodgeFormConj
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_LieModel_IsGrNorm_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_secNorm_iff_chart
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
variable {z : Spec (CommRingCat.of ℂ) ⟶ X}
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {A : HermLine J} {e₀ : Ω}
  {w : (Σ k, J k) → ℂ} {t : Ω} {ν ν' : ℝ}
namespace GlobalTheory.CompanionTheory.Ar
theorem _root_.solution (hz : genPt ξ ⤳ centre z) (he : e₀ ≠ 0) (hw : CoordsAt ξ y z w) {s : MRing J} {b : K → ℕ}
    (hs : IsMultiHomog s b) (hb : ∀ k, A.a k = b k) :
    SecNorm ξ y A e₀ z w (MvPolynomial.aeval y s * e₀) (‖MvPolynomial.aeval w s‖ / A.h w) := by
  choose c hc using hw.1
  have hy := fun k => (hw.2 k (c k) (hc k)).1
  choose r hr hr' using fun p : Σ k, J k => (hw.2 p.1 (c p.1) (hc p.1)).2 p.2
  refine (secNorm_iff_chart he hw c fun k => (hc k).ne_zero).2 ⟨MvPolynomial.aeval r s, ?_, ?_⟩
  · convert CxVal.aeval hz hr s using 1
    have e : y = fun p => y ⟨p.1, c p.1⟩ * (y ⟨p.1, p.2⟩ / y ⟨p.1, c p.1⟩) :=
      funext fun p => (mul_div_cancel₀ _ (hy p.1)).symm
    have e' := aeval_blockScale hs (fun k => y ⟨k, c k⟩) fun p => y ⟨p.1, p.2⟩ / y ⟨p.1, c p.1⟩
    rw [← e] at e'
    have h0 : (∏ k, y ⟨k, c k⟩ ^ b k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
    simp only [hb, zpow_natCast]
    rw [e']
    field_simp
  · have e : w = fun p => w ⟨p.1, c p.1⟩ * r p := funext fun p => (hr' p).trans (mul_comm _ _)
    have e' := aeval_blockScale hs (fun k => w ⟨k, c k⟩) r
    rw [← e] at e'
    rw [div_mul_cancel₀ _ (A.pos w fun k => ⟨c k, (hc k).ne_zero⟩).ne', e']
    simp only [hb, zpow_natCast, norm_mul, norm_prod, norm_pow]
    ring
end GlobalTheory.CompanionTheory.Ar
