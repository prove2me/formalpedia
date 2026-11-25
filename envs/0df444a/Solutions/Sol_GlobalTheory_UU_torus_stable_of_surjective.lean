-- Prove2me | solution 1 for GlobalTheory.UU.torus_stable_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:01:17.810126+00:00
-- url     : https://prove2.me/submissions/464493e5-77ea-4257-9d19-d9acc74a4ae7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableOfSurjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
noncomputable section
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
theorem _root_.solution {S S' : Scheme.{0}} (f : S' ⟶ S) [Surjective f]
    (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G] (G₀ : Over S') [GrpObj G₀]
    (F : G₀.left ⟶ G.left) (hF : IsGrpPullback G₀ G f F)
    (i₀ : splitTorus _ X ⟶ G₀) (i : splitTorus _ X ⟶ G) (hi : TorusCompat f F i₀ i)
    (W : G.left.Opens)
    (hW : (snd (splitTorus _ X) G₀).left ⁻¹ᵁ (F ⁻¹ᵁ W) ≤
      ((fst (splitTorus _ X) G₀ ≫ i₀) * snd _ G₀).left ⁻¹ᵁ (F ⁻¹ᵁ W)) :
    (snd (splitTorus _ X) G).left ⁻¹ᵁ W ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ W := by
  rw [torusCompat_iff] at hi
  let P : Over S := splitTorus S X ⊗ G
  let p : pullback P.hom f ⟶ P.left := pullback.fst P.hom f
  let Z₀ : Over S' := Over.mk (pullback.snd P.hom f)
  have hT := SplitTorus.isPullback_bcMap f X
  have w₁ : (p ≫ (fst (splitTorus S X) G).left) ≫ (splitTorus S X).hom = pullback.snd P.hom f ≫ f := by
    rw [Category.assoc, Over.w]; exact pullback.condition
  have w₂ : (p ≫ (snd (splitTorus S X) G).left) ≫ G.hom = pullback.snd P.hom f ≫ f := by
    rw [Category.assoc, Over.w]; exact pullback.condition
  let t₀ : Z₀ ⟶ splitTorus S' X := Over.homMk (hT.lift _ _ w₁) (hT.lift_snd _ _ w₁)
  let g₀ : Z₀ ⟶ G₀ := Over.homMk (hF.1.lift _ _ w₂) (hF.1.lift_snd _ _ w₂)
  have ht₀ : t₀.left ≫ SplitTorus.bcMap f X = p ≫ (fst (splitTorus S X) G).left := hT.lift_fst _ _ w₁
  have hg₀ : g₀.left ≫ F = p ≫ (snd (splitTorus S X) G).left := hF.1.lift_fst _ _ w₂
  let ρ : Over.mk (Z₀.hom ≫ f) ⟶ P := Over.homMk p pullback.condition
  have h1 : (ρ ≫ fst (splitTorus S X) G ≫ i).left = (t₀ ≫ i₀).left ≫ F := by
    change _ = (t₀.left ≫ i₀.left) ≫ F
    rw [Category.assoc, ← hi, ← Category.assoc t₀.left, ht₀, Category.assoc]; rfl
  have h2 : (ρ ≫ snd (splitTorus S X) G).left = g₀.left ≫ F := hg₀.symm
  have h3 := hF.2 Z₀ (t₀ ≫ i₀) g₀ _ _ h1 h2
  let l : Z₀ ⟶ splitTorus S' X ⊗ G₀ := lift t₀ g₀
  have h4 : p ≫ ((fst (splitTorus S X) G ≫ i) * snd _ G).left =
      l.left ≫ ((fst (splitTorus S' X) G₀ ≫ i₀) * snd _ G₀).left ≫ F := by
    have e : l ≫ ((fst (splitTorus S' X) G₀ ≫ i₀) * snd _ G₀) = (t₀ ≫ i₀) * g₀ := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    rw [← Category.assoc, ← Over.comp_left, e, ← h3, ← MonObj.comp_mul]; rfl
  have h5 : p ≫ (snd (splitTorus S X) G).left = l.left ≫ (snd (splitTorus S' X) G₀).left ≫ F := by
    rw [← Category.assoc, ← Over.comp_left, lift_snd, hg₀]
  have h6 : (p ≫ (snd (splitTorus S X) G).left) ⁻¹ᵁ W ≤
      (p ≫ ((fst (splitTorus S X) G ≫ i) * snd _ G).left) ⁻¹ᵁ W := by
    rw [h4, h5]
    exact fun z hz => hW hz
  intro x hx
  obtain ⟨z, rfl⟩ := p.surjective x
  exact h6 hx
end GlobalTheory.UU
