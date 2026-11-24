-- Prove2me | solution 1 for GlobalTheory.isAffine_and_generated_of_wide_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:01:37.098211+00:00
-- url     : https://prove2.me/submissions/85042226-5d33-496b-a031-c90201cf88ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineAndGeneratedOfWideProduct
import Theorems.Thm_GlobalTheory_AffineProduct_toSpecSubring_subringLift
import Theorems.Thm_GlobalTheory_AffineProduct_subringLift_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open AffineProduct
namespace GlobalTheory
theorem _root_.solution : ∀ (R : CommRingCat.{0}) (j : ℕ) (Y : Scheme.{0}) (D : Fin j → Scheme.{0}) (s : Y ⟶ Spec R) (d : ∀ i, D i ⟶ Spec R) (pr : ∀ i, Y ⟶ D i) (w : ∀ i, pr i ≫ d i = s), (∀ (Z : Scheme.{0}) (z : Z ⟶ Spec R) (f : ∀ i, Z ⟶ D i), (∀ i, f i ≫ d i = z) → ∃! g : Z ⟶ Y, g ≫ s = z ∧ ∀ i, g ≫ pr i = f i) → (∀ i, IsAffine (D i)) → IsAffine Y ∧ ∀ B : Subring Γ(Y, ⊤), (∀ a, s.appTop.hom a ∈ B) → (∀ i a, (pr i).appTop.hom a ∈ B) → B = ⊤ := by
  intro R j Y D s d pr w U hD
  have key : ∀ B : Subring Γ(Y, ⊤), (∀ a, s.appTop.hom a ∈ B) →
      (∀ i a, (pr i).appTop.hom a ∈ B) →
      ∃ g : Spec (CommRingCat.of B) ⟶ Y, toSpecSubring B ≫ g = 𝟙 Y := by
    intro B hs hp
    obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := U _ (subringLift B s hs) (fun i => subringLift B (pr i) (hp i))
      (fun i => subringLift_comp B _ _ _ _ (w i) hs)
    refine ⟨g, (U Y s pr w).unique ⟨?_, fun i => ?_⟩ ⟨by simp, by simp⟩⟩
    · rw [Category.assoc, hg1, toSpecSubring_subringLift]
    · rw [Category.assoc, hg2, toSpecSubring_subringLift]
  constructor
  · obtain ⟨g, hg⟩ := key ⊤ (fun _ => trivial) (fun _ _ => trivial)
    rw [toSpecSubring, Category.assoc] at hg
    set g' := Spec.map (CommRingCat.ofHom (⊤ : Subring Γ(Y, ⊤)).subtype) ≫ g with hg'
    have h1 : g' ≫ Y.toSpecΓ = 𝟙 _ := by
      apply ext_of_isAffine
      have h2 : Y.toSpecΓ ≫ g' ≫ Y.toSpecΓ = Y.toSpecΓ := by
        rw [← Category.assoc, hg, Category.id_comp]
      have h3 := congrArg Scheme.Hom.appTop h2
      rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at h3
      rw [← cancel_mono (Scheme.ΓSpecIso Γ(Y, ⊤)).hom, h3]
      exact (Category.id_comp _).symm
    exact ⟨⟨g', hg, h1⟩⟩
  · intro B hs hp
    obtain ⟨g, hg⟩ := key B hs hp
    have h3 := congrArg Scheme.Hom.appTop hg
    rw [toSpecSubring, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      Scheme.ΓSpecIso_naturality, Scheme.Hom.id_appTop] at h3
    rw [eq_top_iff]
    intro a _
    have h4 := congrArg (fun φ => φ.hom a) h3
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      CommRingCat.hom_id, RingHom.id_apply] at h4
    rw [← h4]
    exact Subtype.property _
end GlobalTheory
