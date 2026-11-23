-- Prove2me | solution 1 for GlobalTheory.eq_comp_section_of_local_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:59.688989+00:00
-- url     : https://prove2.me/submissions/e038d47e-d6f0-4af6-ab35-a6e49431bf37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SurjectiveAppOfIsAbelianScheme
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_P2M_GlobalTheory_isClosedImmersion_equalizer___of_isSeparated_bdcf708e7a7d
import Theorems.Thm_P2M_GlobalTheory_range_subset_range_equalizer___aeb7241b0453
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X T Y S : Scheme.{0}} (p : X ⟶ T) (ε : T ⟶ X)
    (g : X ⟶ Y) (π : T ⟶ S) (q : Y ⟶ S) [IsSeparated q] (he : ε ≫ p = 𝟙 T)
    (hg : g ≫ q = p ≫ π) (hp : IsOpenMap p)
    (hloc : ∀ (t : T) (y : Y), (∀ x : X, p x = t → g x = y) →
      ∃ V : T.Opens, t ∈ V ∧ (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g)
    (hconn : ∀ s : S, _root_.IsPreconnected (π ⁻¹' {s}))
    (hmeet : ∀ s : S, ∃ (t : T) (y : Y), π t = s ∧ ∀ x : X, p x = t → g x = y) :
    g = p ≫ ε ≫ g := by
  have hab : g ≫ q = (p ≫ ε ≫ g) ≫ q := by
    simp only [Category.assoc, hg, reassoc_of% he]
  have hcl := isClosedImmersion_equalizer_ι_of_isSeparated q hab
  let Z : Set X := Set.range (equalizer.ι g (p ≫ ε ≫ g))
  have hZ : IsClosed Z := (equalizer.ι g (p ≫ ε ≫ g)).isClosedEmbedding.isClosed_range
  let T₀ : Set T := (p '' Zᶜ)ᶜ
  have hT₀c : IsClosed T₀ := (hp _ hZ.isOpen_compl).isClosed_compl
  have hfib : ∀ t ∈ T₀, ∀ x : X, p x = t → g x = g (ε t) := by
    intro t ht x hx
    have hxZ : x ∈ Z := by
      by_contra h
      exact ht ⟨x, h, hx⟩
    obtain ⟨z, rfl⟩ := hxZ
    rw [← hx, ← Scheme.Hom.comp_apply, equalizer.condition]
    simp only [Scheme.Hom.comp_apply]
  have hsub : ∀ V : T.Opens, (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g → (V : Set T) ⊆ T₀ := by
    rintro V hV t ht ⟨x, hx, rfl⟩
    exact hx (range_subset_range_equalizer_ι _ hV ⟨⟨x, ht⟩, rfl⟩)
  have hT₀o : IsOpen T₀ := by
    rw [isOpen_iff_forall_mem_open]
    intro t ht
    obtain ⟨V, htV, hV⟩ := hloc t _ (hfib t ht)
    exact ⟨V, hsub V hV, V.2, htV⟩
  have hall : ∀ t : T, t ∈ T₀ := by
    intro t
    obtain ⟨t', y, ht', hy⟩ := hmeet (π t)
    obtain ⟨V, htV, hV⟩ := hloc t' y hy
    exact (hconn (π t)).subset_isClopen ⟨hT₀c, hT₀o⟩ ⟨t', ht', hsub V hV htV⟩ rfl
  refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
  obtain ⟨V, htV, hV⟩ := hloc (p x) _ (hfib _ (hall _))
  exact ⟨p ⁻¹ᵁ V, htV, hV⟩
end GlobalTheory
