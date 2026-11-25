-- Prove2me | solution 1 for GlobalTheory.UU.IsWt.pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:12:33.021505+00:00
-- url     : https://prove2.me/submissions/b8764247-01db-48bd-ace3-15e8ee344d7a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ESecCompOfIsGrpPullback
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S S' : Scheme.{0}} {f : S' ⟶ S}
namespace GlobalTheory.UU
namespace IsWt
theorem _root_.solution {X : Type} [AddCommGroup X] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'}
    (hi : TorusCompat f F i' i) {V : G.left.Opens} {V' : G'.left.Opens} (hV : V' ≤ F ⁻¹ᵁ V) {u : Γ(G.left, V)}
    {χ : X} (hu : IsWt i V u χ) : IsWt i' V' ((F.appLE V V' hV).hom u) χ := by
  obtain ⟨τ, hτ, hχ, hτi⟩ := hi
  intro Z' t' g' h₁ h₂
  let Z : Over S := Over.mk (Z'.hom ≫ f)
  let t : Z ⟶ splitTorus S X := Over.homMk (t'.left ≫ τ) (by
    show (t'.left ≫ τ) ≫ (splitTorus S X).hom = Z'.hom ≫ f
    rw [Category.assoc, hτ, ← Category.assoc, Over.w])
  let g : Z ⟶ G := Over.homMk (g'.left ≫ F) (by
    show (g'.left ≫ F) ≫ G.hom = Z'.hom ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, Over.w])
  let x₀ : Z ⟶ G := Over.homMk ((t' ≫ i').left ≫ F) (by
    show ((t' ≫ i').left ≫ F) ≫ G.hom = Z'.hom ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, Over.w])
  have hx₀ : t ≫ i = x₀ := by
    apply Over.OverMorphism.ext
    simp only [t, x₀, Over.comp_left, Over.homMk_left, Category.assoc, hτi]
  have hmul : (t ≫ i * g).left = (t' ≫ i' * g').left ≫ F := by
    rw [hx₀]
    exact hF.2 Z' (t' ≫ i') g' x₀ g rfl rfl
  have h₁' : ⊤ ≤ (t ≫ i * g).left ⁻¹ᵁ V := by
    rw [hmul]
    intro x _
    exact hV (h₁ trivial)
  have h₂' : ⊤ ≤ g.left ⁻¹ᵁ V := by
    intro x _
    exact hV (h₂ trivial)
  have key := hu Z t g h₁' h₂'
  have hcong : ∀ (a b : Z'.left ⟶ G.left) (hab : a = b) (ha : ⊤ ≤ a ⁻¹ᵁ V) (hb : ⊤ ≤ b ⁻¹ᵁ V),
      (a.appLE V ⊤ ha).hom u = (b.appLE V ⊤ hb).hom u := by
    intro a b hab ha hb
    subst hab
    rfl
  have e1 : ((t' ≫ i' * g').left.appLE V' ⊤ h₁).hom ((F.appLE V V' hV).hom u) =
      (((t' ≫ i' * g').left ≫ F).appLE V ⊤ (by intro x _; exact hV (h₁ trivial))).hom u := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have e2 : (g'.left.appLE V' ⊤ h₂).hom ((F.appLE V V' hV).hom u) =
      ((g'.left ≫ F).appLE V ⊤ (by intro x _; exact hV (h₂ trivial))).hom u := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have hc : (t.left.appTop).hom (charUnit S X χ).val = (t'.left.appTop).hom (charUnit S' X χ).val := by
    show ((t'.left ≫ τ).appTop).hom _ = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hχ]
  rw [e1, e2]
  exact (hcong _ _ hmul.symm _ h₁').trans (key.trans (congrArg₂ (· * ·) hc (hcong _ _ rfl h₂' _)))
end IsWt
end GlobalTheory.UU
