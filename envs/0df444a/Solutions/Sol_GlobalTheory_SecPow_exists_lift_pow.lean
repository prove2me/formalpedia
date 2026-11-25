-- Prove2me | solution 1 for GlobalTheory.SecPow.exists_lift_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:11:53.584981+00:00
-- url     : https://prove2.me/submissions/bfe8bcd5-f5b9-4114-bf9e-c4fbc00375f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowSection
import Theorems.Thm_GlobalTheory_SecPow_add_pow_succ_of_mul_self
import Theorems.Thm_GlobalTheory_SecPow_eq_of_preimage_eq
import Theorems.Thm_GlobalTheory_SecPow_app_rs
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.SecPow
variable {X X' : Scheme.{0}}
namespace GlobalTheory.SecPow
theorem _root_.solution (β : X' ⟶ X) [IsClosedImmersion β] [Surjective β]
    (hsq : ∀ (W : X.Opens) (x y : Γ(X, W)), (β.app W).hom x = 0 → (β.app W).hom y = 0 → x * y = 0)
    {V O : X.Opens} (hV : IsAffineOpen V) (hO : O ≤ V) (τ : Γ(X, O)) (s : Γ(X', β ⁻¹ᵁ V))
    (hs : X'.basicOpen s = β ⁻¹ᵁ O) (hτ : (β.app O).hom τ = rs X' (β.preimage_mono hO) s) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∃ σ : Γ(X, V), (β.app V).hom σ = s ^ k ∧ rs X hO σ = τ ^ k := by
  obtain ⟨t, rfl⟩ : ∃ t, (β.app V).hom t = s := β.app_surjective V hV s
  obtain rfl : X.basicOpen t = O :=
    eq_of_preimage_eq β ((Scheme.preimage_basicOpen β t).trans hs)
  have hε : (β.app _).hom (τ - rs X hO t) = 0 := by
    rw [map_sub, hτ, app_rs, sub_self]
  obtain ⟨n, w, hw⟩ : ∃ (n : ℕ) (w : Γ(X, V)), rs X hO w = rs X hO t ^ n * (τ - rs X hO t) :=
    exists_eq_pow_mul_of_isAffineOpen X V hV t (τ - rs X hO t)
  have h₁ : rs X' (β.preimage_mono hO) ((β.app V).hom w) = 0 := by
    rw [← app_rs β hO, hw, map_mul, hε, mul_zero]
  obtain ⟨l, hl⟩ : ∃ l : ℕ, (β.app V).hom t ^ l * (β.app V).hom w = 0 := by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X' (hV.preimage β) _ _ ?_
    have := congrArg (rs X' hs.le) h₁
    rw [rs_rs, map_zero] at this
    exact this
  refine ⟨n + l + 1, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = (n + l + j) + 1 := ⟨k - (n + l + 1), by omega⟩
  refine ⟨t ^ (n + l + j + 1) + ((n + l + j + 1 : ℕ) : Γ(X, V)) * (t ^ j * (t ^ l * w)), ?_, ?_⟩
  · simp only [map_add, map_mul, map_pow, hl, mul_zero, add_zero]
  · have e := add_pow_succ_of_mul_self (rs X hO t) (τ - rs X hO t) (hsq _ _ _ hε hε) (n + l + j)
    rw [add_sub_cancel] at e
    rw [e, map_add, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_natCast, hw]
    ring
end GlobalTheory.SecPow
