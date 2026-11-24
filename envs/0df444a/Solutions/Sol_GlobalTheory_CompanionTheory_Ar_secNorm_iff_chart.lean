-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.secNorm_iff_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:50:58.96181+00:00
-- url     : https://prove2.me/submissions/83811cd2-4f7b-4685-90fd-b608a00730cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_HodgeIPIffHodgeFormConj
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CxVal_one
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CxVal_zpow

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
theorem _root_.solution (he : e₀ ≠ 0) (hw : CoordsAt ξ y z w) (c : (k : K) → J k) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    SecNorm ξ y A e₀ z w t ν ↔ ∃ u : ℂ, ValAt ξ z (t / ((∏ k, y ⟨k, c k⟩ ^ A.a k) * e₀)) u ∧
      ν * A.h w = ‖u‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ A.a k := by
  refine ⟨fun h => h.2.2 c hc, ?_⟩
  rintro ⟨u, hu, hν⟩
  refine ⟨he, hw, fun c' hc' => ?_⟩
  choose r hr hr' using fun k => (hw.2 k (c' k) (IsUnit.mk0 _ (hc' k))).2 (c k)
  have hr0 : ∀ k, r k ≠ 0 := fun k h => hc k (by rw [hr', h, zero_mul])
  have hp : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ A.a k) (∏ k ∈ s, r k ^ A.a k) := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using CxVal.one hu.1
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.prod_insert hk]
      exact CxVal.mul (CxVal.zpow (hr k) (hr0 k) _) ih
  have hy : (∏ k, y ⟨k, c k⟩ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw.2 k (c k) (IsUnit.mk0 _ (hc k))).1
  refine ⟨u * ∏ k, r k ^ A.a k, ?_, ?_⟩
  · convert CxVal.mul hu (hp Finset.univ) using 1
    simp only [div_zpow, Finset.prod_div_distrib]
    simp only [div_eq_mul_inv, mul_inv]
    field_simp
  · rw [hν, norm_mul, norm_prod, _root_.mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hr' k, norm_mul, mul_zpow, norm_zpow]
end GlobalTheory.CompanionTheory.Ar
