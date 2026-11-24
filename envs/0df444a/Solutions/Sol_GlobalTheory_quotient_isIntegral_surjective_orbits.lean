-- Prove2me | solution 1 for GlobalTheory.quotient_isIntegral_surjective_orbits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:26:19.905801+00:00
-- url     : https://prove2.me/submissions/73576ae5-5734-4081-b7fb-201c9d146f1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Theorems.Thm_GlobalTheory_exists_aut_of_comp_eq_of_invariant
import Theorems.Thm_GlobalTheory_isIntegralHom_of_invariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsIntegralHom π ∧ Surjective π ∧ (∀ x y : X, π x = π y → ∃ g, y = (ρ g).hom x) ∧ (∀ (k : Type) [Field k] (x y : Sp k ⟶ X), x ≫ π = y ≫ π → ∃ g, y = x ≫ (ρ g).hom) ∧ ∀ U : X.Opens, (∀ g, (ρ g).hom ⁻¹ᵁ U = U) → ∃ V : X'.Opens, π ⁻¹ᵁ V = U := by
  intro Γ _ _ X X' ρ π ⟨hAff, hπ, hV⟩
  have hinvAll : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W) := by
    intro W _ s hs
    apply (hV W).2 s
    intro g h
    obtain ⟨h', e⟩ := hs g
    exact e
  have hInt : IsIntegralHom π := isIntegralHom_of_invariant ρ π hπ hinvAll
  have hfield : ∀ (k : Type) [Field k] (x y : Sp k ⟶ X), x ≫ π = y ≫ π →
      ∃ g, y = x ≫ (ρ g).hom := by
    intro k _ x y hxy
    let p₀ : Sp k := ⟨⊥, Ideal.isPrime_bot⟩
    obtain ⟨W, hW, hmem, -⟩ :=
      exists_isAffineOpen_mem_and_subset (x := (x ≫ π) p₀) (U := ⊤) trivial
    refine exists_aut_of_comp_eq_of_invariant ρ π hπ hW (hinvAll W hW) x y hxy ?_
    intro p _
    have hp : p = p₀ := Subsingleton.elim _ _
    subst hp
    exact hmem
  have hpts : ∀ x y : X, π x = π y → ∃ g, y = (ρ g).hom x := by
    intro x y hxy
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
    have hab : (Scheme.fromSpecResidueField _ z ≫ pullback.fst π π) ≫ π =
        (Scheme.fromSpecResidueField _ z ≫ pullback.snd π π) ≫ π := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨g, hg⟩ := hfield ((pullback π π).residueField z) _ _ hab
    refine ⟨g, ?_⟩
    let s : Spec ((pullback π π).residueField z) := ⟨⊥, Ideal.isPrime_bot⟩
    have ha : (Scheme.fromSpecResidueField _ z ≫ pullback.fst π π) s = x := by
      show pullback.fst π π (Scheme.fromSpecResidueField _ z s) = x
      rw [Scheme.fromSpecResidueField_apply]
      exact hz1
    have hb : (Scheme.fromSpecResidueField _ z ≫ pullback.snd π π) s = y := by
      show pullback.snd π π (Scheme.fromSpecResidueField _ z s) = y
      rw [Scheme.fromSpecResidueField_apply]
      exact hz2
    rw [← hb, hg, ← ha]
    rfl
  have hsurj : Surjective π := by
    rw [surjective_iff]
    intro y
    obtain ⟨W, hW, hmem, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
    have hA : IsAffineOpen (π ⁻¹ᵁ W) := hW.preimage π
    have heq := IsAffineOpen.SpecMap_appLE_fromSpec π hW hA le_rfl
    have hmem' : y ∈ Set.range hW.fromSpec := by
      rw [hW.range_fromSpec]
      exact hmem
    obtain ⟨p, rfl⟩ := hmem'
    have hint : (π.appLE W (π ⁻¹ᵁ W) le_rfl).hom.IsIntegral := by
      rw [← Scheme.Hom.app_eq_appLE]
      exact hInt.isIntegral_app W hW
    have hinj : Function.Injective (π.appLE W (π ⁻¹ᵁ W) le_rfl).hom := by
      rw [← Scheme.Hom.app_eq_appLE]
      exact (hV W).1
    obtain ⟨q, hq⟩ := hint.comap_surjective hinj p
    refine ⟨hA.fromSpec q, ?_⟩
    have := congrArg (fun f => f q) heq
    rw [← hq]
    exact this.symm
  have hopen : ∀ U : X.Opens, (∀ g, (ρ g).hom ⁻¹ᵁ U = U) → ∃ V : X'.Opens, π ⁻¹ᵁ V = U := by
    intro U hU
    have hcl : IsClosed (π '' (U : Set X)ᶜ) := π.isClosedMap _ U.isOpen.isClosed_compl
    refine ⟨⟨(π '' (U : Set X)ᶜ)ᶜ, hcl.isOpen_compl⟩, ?_⟩
    ext x
    show π x ∈ (π '' (U : Set X)ᶜ)ᶜ ↔ x ∈ U
    constructor
    · intro h
      by_contra hx
      exact h ⟨x, hx, rfl⟩
    · rintro hx ⟨y, hy, hxy⟩
      obtain ⟨g, rfl⟩ := hpts x y hxy.symm
      apply hy
      have hx' : x ∈ (ρ g).hom ⁻¹ᵁ U := by
        rw [hU g]
        exact hx
      exact hx'
  exact ⟨hInt, hsurj, hpts, hfield, hopen⟩
end GlobalTheory
