-- Prove2me | solution 1 for GlobalTheory.exists_units_of_isLimit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:06:07.772465+00:00
-- url     : https://prove2.me/submissions/538759d2-e1de-461c-8b9c-5ef5d3bd017b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Theorems.Thm_GlobalTheory_gm_id_pullU
import Theorems.Thm_GlobalTheory_gm_res_pullU
import Theorems.Thm_GlobalTheory_gm_pullU_mul_res
import Theorems.Thm_GlobalTheory_exists_common_refinement
import Theorems.Thm_P2M_GlobalTheory_exists_unit___eq_ea6a0a298c88
import Theorems.Thm_GlobalTheory_exists_pullU_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
variable {I : Type} [SmallCategory I] [IsCofiltered I]
variable (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
include hc
namespace GlobalTheory
theorem _root_.solution {i : I} [QuasiSeparatedSpace (D.obj i)] {A : Type} [Finite A]
    (V : A → (D.obj i).Opens) (hV : ∀ a, IsAffineOpen (V a)) (G : ∀ a b, Γ(D.obj i, V a ⊓ V b)ˣ)
    (s : ∀ a, Γ(X, π i ⁻¹ᵁ V a)ˣ)
    (hs : ∀ a b (y : X), y ∈ π i ⁻¹ᵁ V a → y ∈ π i ⁻¹ᵁ V b →
      gm (𝟙 X) y _ (s a) = gm (π i) y _ (G a b) * gm (𝟙 X) y _ (s b)) :
    ∃ (j : I) (f : j ⟶ i) (u : ∀ a, Γ(D.obj j, D.map f ⁻¹ᵁ V a)ˣ),
      ∀ a b (y : D.obj j), y ∈ D.map f ⁻¹ᵁ V a → y ∈ D.map f ⁻¹ᵁ V b →
        gm (𝟙 _) y _ (u a) = gm (D.map f) y _ (G a b) * gm (𝟙 _) y _ (u b) := by
  have le : ∀ {j k : I} (f : j ⟶ i) (g : k ⟶ j) (U : (D.obj i).Opens),
      D.map (g ≫ f) ⁻¹ᵁ U ≤ D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ U) := fun f g U => by
    rw [D.map_comp, Scheme.Hom.comp_preimage]
  obtain ⟨j, f, hj⟩ := exists_common_refinement (i := i)
    (fun a j f => ∃ t : Γ(D.obj j, D.map f ⁻¹ᵁ V a)ˣ, ∀ y : X, y ∈ π i ⁻¹ᵁ V a →
      gm (π j) y (D.map f ⁻¹ᵁ V a) t = gm (𝟙 X) y (π i ⁻¹ᵁ V a) (s a))
    (by
      rintro a j f k g ⟨t, ht⟩
      refine ⟨res (le f g _) (pullU (D.map g) _ t), fun y hy => ?_⟩
      have hy' := cone_preimage_le D π w (g ≫ f) _ hy
      refine (gm_res_pullU (π k) (D.map g) y (le f g (V a)) hy' t).trans ?_
      rw [w g]
      exact ht y hy)
    (fun a => exists_unit_π_eq D π w hc (hV a) (s a))
  choose t ht using hj
  have l₁ : ∀ a b, D.map f ⁻¹ᵁ (V a ⊓ V b) ≤ D.map f ⁻¹ᵁ V a := fun a b _ hy => hy.1
  have l₂ : ∀ a b, D.map f ⁻¹ᵁ (V a ⊓ V b) ≤ D.map f ⁻¹ᵁ V b := fun a b _ hy => hy.2
  obtain ⟨k, g, hk⟩ := exists_common_refinement (i := j)
    (fun (p : A × A) k g => pullU (D.map g) _ (res (l₁ p.1 p.2) (t p.1)) =
      pullU (D.map g) _ (pullU (D.map f) _ (G p.1 p.2) * res (l₂ p.1 p.2) (t p.2)))
    (by
      intro p k g k' g' h
      rw [D.map_comp]
      exact congrArg (pullU (D.map g') _) h)
    (by
      rintro ⟨a, b⟩
      refine exists_pullU_eq D π w hc ?_ _ _ fun y hy => ?_
      · exact QuasiCompact.isCompact_preimage (f := D.map f) _ (V a ⊓ V b).isOpen
          (QuasiSeparatedSpace.inter_isCompact _ _ (V a).isOpen (hV a).isCompact (V b).isOpen
            (hV b).isCompact)
      · have hy' : y ∈ π i ⁻¹ᵁ (V a ⊓ V b) := by
          rw [← w f]; exact hy
        refine (gm_res (π j) y (l₁ a b) hy (t a)).trans (Eq.trans ?_
          (gm_pullU_mul_res (π j) (D.map f) y (l₂ a b) hy (G a b) (t b)).symm)
        rw [ht a y hy'.1, ht b y hy'.2, w f]
        exact hs a b y hy'.1 hy'.2)
  refine ⟨k, g ≫ f, fun a => res (le f g _) (pullU (D.map g) _ (t a)), fun a b y ha hb => ?_⟩
  have hy : D.map g y ∈ D.map f ⁻¹ᵁ (V a ⊓ V b) := ⟨le f g _ ha, le f g _ hb⟩
  have val : ∀ a, y ∈ D.map (g ≫ f) ⁻¹ᵁ V a →
      gm (𝟙 (D.obj k)) y (D.map (g ≫ f) ⁻¹ᵁ V a) (res (le f g (V a)) (pullU (D.map g) _ (t a))) =
        gm (D.map g) y (D.map f ⁻¹ᵁ V a) (t a) :=
    fun a ha => (gm_res_pullU (𝟙 _) (D.map g) y (le f g (V a)) ha (t a)).trans (by rw [Category.id_comp])
  have e := (gm_id_pullU (D.map g) y _ hy _).symm.trans
    ((congrArg (gm (𝟙 (D.obj k)) y (D.map g ⁻¹ᵁ D.map f ⁻¹ᵁ (V a ⊓ V b))) (hk (a, b))).trans
      (gm_id_pullU (D.map g) y _ hy _))
  have e' := (gm_res (D.map g) y (l₁ a b) hy (t a)).symm.trans (e.trans
    (gm_pullU_mul_res (D.map g) (D.map f) y (l₂ a b) hy (G a b) (t b)))
  refine (val a ha).trans (e'.trans (congrArg₂ (· * ·) ?_ (val b hb).symm))
  rw [D.map_comp]
end GlobalTheory
