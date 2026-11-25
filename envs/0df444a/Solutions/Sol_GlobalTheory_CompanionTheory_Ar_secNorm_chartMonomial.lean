-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.secNorm_chartMonomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:44:32.257638+00:00
-- url     : https://prove2.me/submissions/be7f9c01-25a7-49f8-bdef-28a7c4d8e255

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_HodgeIPIffHodgeFormConj
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_LieModel_IsGrNorm_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CxVal_one
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_secNorm_iff_chart

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
theorem _root_.solution (hz : genPt ξ ⤳ centre z) (he : e₀ ≠ 0) (hw : CoordsAt ξ y z w) (c : (k : K) → J k)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    SecNorm ξ y A e₀ z w ((∏ k, y ⟨k, c k⟩ ^ A.a k) * e₀) ((∏ k, ‖w ⟨k, c k⟩‖ ^ A.a k) / A.h w) := by
  have hy : (∏ k, y ⟨k, c k⟩ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw.2 k (c k) (IsUnit.mk0 _ (hc k))).1
  refine (secNorm_iff_chart he hw c hc).2 ⟨1, ?_, ?_⟩
  · rw [div_self (mul_ne_zero hy he)]
    exact CxVal.one hz
  · rw [div_mul_cancel₀ _ (A.pos w fun k => ⟨c k, hc k⟩).ne']
    simp
end GlobalTheory.CompanionTheory.Ar
