-- Prove2me | solution 1 for GlobalTheory.FGAbove.exists_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:38:36.785848+00:00
-- url     : https://prove2.me/submissions/89361003-f0c9-4e7a-b61b-634cf38e73b4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Theorems.Thm_GlobalTheory_FGAbove_exists_ge
import Theorems.Thm_GlobalTheory_FGAbove_exists_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C]
variable {R₀ : Subalgebra k C}
namespace GlobalTheory
namespace FGAbove
theorem _root_.solution (h : R₀.FG) {S : Type} [CommRing S] (φ : ∀ R : FGAbove R₀, R.1 →+* S)
    (hφ : ∀ (R T : FGAbove R₀) (hRT : R.1 ≤ T.1) (x : R.1), φ T (Subalgebra.inclusion hRT x) = φ R x) :
    ∃ ψ : C →+* S, ∀ (R : FGAbove R₀) (x : R.1), ψ x = φ R x := by
  choose P hP using FGAbove.exists_mem h
  have key : ∀ (R : FGAbove R₀) (x : C) (hx : x ∈ R.1), φ (P x) ⟨x, hP x⟩ = φ R ⟨x, hx⟩ := by
    intro R x hx
    obtain ⟨T, h₁, h₂⟩ := FGAbove.exists_ge R (P x)
    exact (hφ _ T h₂ _).symm.trans (hφ _ T h₁ ⟨x, hx⟩)
  have two : ∀ x y : C, ∃ T : FGAbove R₀, x ∈ T.1 ∧ y ∈ T.1 := fun x y => by
    obtain ⟨T, h₁, h₂⟩ := FGAbove.exists_ge (P x) (P y)
    exact ⟨T, h₁ (hP x), h₂ (hP y)⟩
  refine ⟨⟨⟨⟨fun x => φ (P x) ⟨x, hP x⟩, map_one (φ (P 1))⟩, fun x y => ?_⟩, map_zero (φ (P 0)),
    fun x y => ?_⟩, fun R x => key R x x.2⟩
  · obtain ⟨T, hx, hy⟩ := two x y
    show φ _ _ = φ _ _ * φ _ _
    rw [key T x hx, key T y hy, key T _ (mul_mem hx hy), ← map_mul]
    rfl
  · obtain ⟨T, hx, hy⟩ := two x y
    show φ _ _ = φ _ _ + φ _ _
    rw [key T x hx, key T y hy, key T _ (add_mem hx hy), ← map_add]
    rfl
end FGAbove
end GlobalTheory
