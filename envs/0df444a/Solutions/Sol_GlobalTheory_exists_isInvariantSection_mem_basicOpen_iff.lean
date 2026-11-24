-- Prove2me | solution 1 for GlobalTheory.exists_isInvariantSection_mem_basicOpen_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:04:54.606191+00:00
-- url     : https://prove2.me/submissions/f17fe1d8-e048-4146-8806-93e658a569e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
import Theorems.Thm_GlobalTheory_aut_map_one_apply
import Theorems.Thm_GlobalTheory_IsInvariantSection_basicOpen_le
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor


section
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace GlobalTheory
section FiniteSets
variable {X Y : Scheme.{u}}
namespace FiniteSubsetsInAffineOpens
end FiniteSubsetsInAffineOpens
end FiniteSets
section Orbits
variable {G : Type v} [Group G] {X Y : Scheme.{u}}
namespace OrbitsInAffineOpens
end OrbitsInAffineOpens
variable {ρ : G →* Aut X}
private theorem mem_basicOpen_prod_iff {U : X.Opens} (a : G → Γ(X, U)) (T : Finset G) (x : X) :
    x ∈ X.basicOpen (∏ g ∈ T, a g) ↔ x ∈ U ∧ ∀ g ∈ T, x ∈ X.basicOpen (a g) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert g T hg ih =>
    rw [Finset.prod_insert hg, Scheme.basicOpen_mul, TopologicalSpace.Opens.mem_inf, ih,
      Finset.forall_mem_insert]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h2, h1, h3⟩
    · rintro ⟨h2, h1, h3⟩
      exact ⟨h1, h2, h3⟩
private theorem appLE_apply_congr' {f f' : X ⟶ X} (hff : f = f') (U : X.Opens) (e : U ≤ f ⁻¹ᵁ U)
    (e' : U ≤ f' ⁻¹ᵁ U) (s : Γ(X, U)) : f.appLE U U e s = f'.appLE U U e' s := by
  subst hff
  rfl
variable [Finite G]
end Orbits
end GlobalTheory
end

set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type v} [Group G] {X Y : Scheme.{u}}
variable {ρ : G →* Aut X}
namespace GlobalTheory
theorem _root_.solution [Finite G] {U : X.Opens}
    (hU : ∀ g, U ≤ (ρ g).hom ⁻¹ᵁ U) (s : Γ(X, U)) :
    ∃ t : Γ(X, U), IsInvariantSection ρ U t ∧
      ∀ x, x ∈ X.basicOpen t ↔ ∀ g, (ρ g).hom x ∈ X.basicOpen s := by
  classical
  have := Fintype.ofFinite G
  refine ⟨∏ g : G, (ρ g).hom.appLE U U (hU g) s, fun k ↦ ⟨hU k, ?_⟩, fun x ↦ ?_⟩
  · rw [map_prod]
    refine (Finset.prod_congr rfl fun g _ ↦ ?_).trans (Fintype.prod_equiv (Equiv.mulRight k)
      (fun g ↦ (ρ (g * k)).hom.appLE U U (hU (g * k)) s) _ (fun _ ↦ rfl))
    have e := Scheme.Hom.appLE_comp_appLE (ρ k).hom (ρ g).hom U U U (hU g) (hU k)
    have e' := congrArg (fun φ : Γ(X, U) ⟶ Γ(X, U) ↦ φ s) e
    simp only [CommRingCat.comp_apply] at e'
    rw [e']
    exact appLE_apply_congr' (by rw [map_mul, Aut.Aut_mul_def]; rfl) _ _ _ _
  · rw [mem_basicOpen_prod_iff]
    have key : ∀ g, x ∈ X.basicOpen ((ρ g).hom.appLE U U (hU g) s) ↔
        x ∈ U ∧ (ρ g).hom x ∈ X.basicOpen s := fun g ↦ by
      rw [Scheme.basicOpen_appLE]
      exact Iff.rfl
    simp only [Finset.mem_univ, true_implies, key]
    constructor
    · rintro ⟨_, h⟩ g
      exact (h g).2
    · intro h
      have h1 := h 1
      rw [aut_map_one_apply] at h1
      exact ⟨X.basicOpen_le s h1, fun g ↦ ⟨X.basicOpen_le s h1, h g⟩⟩
end GlobalTheory
