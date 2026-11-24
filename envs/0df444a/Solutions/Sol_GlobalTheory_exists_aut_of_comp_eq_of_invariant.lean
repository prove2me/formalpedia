-- Prove2me | solution 1 for GlobalTheory.exists_aut_of_comp_eq_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:07:20.825805+00:00
-- url     : https://prove2.me/submissions/11fc969b-8dc2-4645-9ad0-6a09e24e8567

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Theorems.Thm_GlobalTheory_exists_smul_eq_of_eq_on_invariants

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
theorem _root_.solution {G : Type*} [Group G] [Finite G] {X X' T : Scheme.{0}}
    (ρ : G →* Aut X) (π : X ⟶ X') [IsAffineHom π] (hπ : ∀ g, (ρ g).hom ≫ π = π)
    {W : X'.Opens} (hW : IsAffineOpen W)
    (hinv : ∀ s : Γ(X, π ⁻¹ᵁ W), IsInvariantSection ρ _ s → s ∈ Set.range (π.app W))
    [IsAffine T] [IsIntegral T] (x y : T ⟶ X) (hxy : x ≫ π = y ≫ π)
    (hx : ⊤ ≤ x ⁻¹ᵁ π ⁻¹ᵁ W) : ∃ g, y = x ≫ (ρ g).hom := by
  have hU : ∀ g, π ⁻¹ᵁ W ≤ (ρ g).hom ⁻¹ᵁ π ⁻¹ᵁ W := fun g => by
    show _ ≤ ((ρ g).hom ≫ π) ⁻¹ᵁ W
    rw [hπ g]
  let _ := sectionsAction ρ _ hU
  have hact : ∀ (g : G) (s : Γ(X, π ⁻¹ᵁ W)),
      g • s = (ρ g⁻¹).hom.appLE _ _ (hU g⁻¹) s := fun g s => rfl
  have hy : ⊤ ≤ y ⁻¹ᵁ π ⁻¹ᵁ W := by
    show ⊤ ≤ (y ≫ π) ⁻¹ᵁ W
    rw [← hxy]
    exact hx
  have key : ∀ (f f' : T ⟶ X') (_ : f = f') (h1 : ⊤ ≤ f ⁻¹ᵁ W) (h2 : ⊤ ≤ f' ⁻¹ᵁ W),
      f.appLE W ⊤ h1 = f'.appLE W ⊤ h2 := by
    rintro f f' rfl h1 h2
    rfl
  have hagree : ∀ s : Γ(X, π ⁻¹ᵁ W), (∀ g : G, g • s = s) →
      (x.appLE (π ⁻¹ᵁ W) ⊤ hx).hom s = (y.appLE (π ⁻¹ᵁ W) ⊤ hy).hom s := by
    intro s hs
    have hinv' : IsInvariantSection ρ _ s := by
      intro g
      refine ⟨hU g, ?_⟩
      have := hs g⁻¹
      rw [hact] at this
      simpa only [inv_inv] using this
    obtain ⟨t, rfl⟩ := hinv s hinv'
    have e1 := Scheme.Hom.comp_appLE x π W ⊤ hx
    have e2 := Scheme.Hom.comp_appLE y π W ⊤ hy
    have := congrArg (fun φ => φ.hom t) (key _ _ hxy hx hy)
    rw [e1, e2] at this
    exact this
  obtain ⟨g, hg⟩ := exists_smul_eq_of_eq_on_invariants (G := G) _ _ hagree
  refine ⟨g⁻¹, ?_⟩
  have h' : ⊤ ≤ (x ≫ (ρ g⁻¹).hom) ⁻¹ᵁ π ⁻¹ᵁ W := by
    show ⊤ ≤ x ⁻¹ᵁ ((ρ g⁻¹).hom ⁻¹ᵁ π ⁻¹ᵁ W)
    exact hx.trans (x.preimage_mono (hU g⁻¹))
  have heq : y.appLE (π ⁻¹ᵁ W) ⊤ hy = (x ≫ (ρ g⁻¹).hom).appLE (π ⁻¹ᵁ W) ⊤ h' := by
    ext s
    rw [← Scheme.Hom.appLE_comp_appLE x (ρ g⁻¹).hom _ _ _ (hU g⁻¹) hx]
    rw [hg s, hact]
    rfl
  have hA : IsAffineOpen (π ⁻¹ᵁ W) := hW.preimage π
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec y hA (isAffineOpen_top T) hy
  have h2 := IsAffineOpen.SpecMap_appLE_fromSpec (x ≫ (ρ g⁻¹).hom) hA (isAffineOpen_top T) h'
  rw [heq] at h1
  rw [IsAffineOpen.fromSpec_top] at h1 h2
  exact (cancel_epi _).1 (h1.symm.trans h2)
end GlobalTheory
