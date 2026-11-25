-- Prove2me | solution 1 for GlobalTheory.TorusCube.exists_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:51:12.659532+00:00
-- url     : https://prove2.me/submissions/cdd2db24-b761-4fd2-97a5-a033b473967c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SplitTorusGenCubical
import Theorems.Thm_GlobalTheory_TorusCube_toHom_comp_val
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_appTop_comp_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_over_appTop_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torus_units
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusCube
open Rosenlicht SplitTorusPoints Geo.Tor
namespace GlobalTheory.TorusCube
theorem _root_.solution (k : Type) [Field k] (X : Type) [AddCommGroup X] [TwoUniqueSums (X × X × X)]
    (w : Γ((splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗
      splitTorus (Spec (.of k)) X).left, ⊤)) (hw : IsUnit w) :
    ∃ (c : Γ(Spec (.of k), ⊤)) (a b d : X), IsUnit c ∧
      ∀ (Z : Over (Spec (.of k))) (x y u : Z ⟶ splitTorus (Spec (.of k)) X),
        (lift x (lift y u)).left.appTop.hom w = Z.hom.appTop.hom c *
          ((toHom x (Multiplicative.ofAdd a)).val * (toHom y (Multiplicative.ofAdd b)).val *
            (toHom u (Multiplicative.ofAdd d)).val) := by
  let Y := splitTorus (Spec (.of k)) (X × X × X)
  have hp : ∀ j : X →+ X × X × X, ∃ p : Y ⟶ splitTorus (Spec (.of k)) X,
      ∀ (Z : Over (Spec (.of k))) (ρ : Z ⟶ Y) (a : X),
        toHom (ρ ≫ p) (Multiplicative.ofAdd a) = toHom ρ (Multiplicative.ofAdd (j a)) := by
    intro j
    obtain ⟨p, hp⟩ := (toHom_bijective (Z := Y) (X := X)).2
      ((toHom (𝟙 Y)).comp (AddMonoidHom.toMultiplicative j))
    refine ⟨p, fun Z ρ a => Units.ext ?_⟩
    rw [toHom_comp_val, hp]
    conv_rhs => rw [← Category.comp_id ρ, toHom_comp_val]
    rfl
  obtain ⟨p₀, h₀⟩ := hp (AddMonoidHom.inl _ _)
  obtain ⟨p₁, h₁⟩ := hp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inl _ _))
  obtain ⟨p₂, h₂⟩ := hp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inr _ _))
  obtain ⟨c, ⟨a, b, d⟩, hc, e⟩ := torus_units k (X × X × X)
    (hw.map (lift p₀ (lift p₁ p₂)).left.appTop.hom)
  refine ⟨c, a, b, d, hc, fun Z x y u => ?_⟩
  obtain ⟨ρ, hρ⟩ := (toHom_bijective (Z := Z) (X := X × X × X)).2
    ((toHom x).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst _ _)) *
      (toHom y).comp (AddMonoidHom.toMultiplicative
        ((AddMonoidHom.fst _ _).comp (AddMonoidHom.snd _ _))) *
      (toHom u).comp (AddMonoidHom.toMultiplicative
        ((AddMonoidHom.snd _ _).comp (AddMonoidHom.snd _ _))))
  have r₀ : ρ ≫ p₀ = x := toHom_bijective.1 (MonoidHom.ext fun a => by
    refine (h₀ Z ρ a.toAdd).trans ?_
    rw [hρ]; simp)
  have r₁ : ρ ≫ p₁ = y := toHom_bijective.1 (MonoidHom.ext fun a => by
    refine (h₁ Z ρ a.toAdd).trans ?_
    rw [hρ]; simp)
  have r₂ : ρ ≫ p₂ = u := toHom_bijective.1 (MonoidHom.ext fun a => by
    refine (h₂ Z ρ a.toAdd).trans ?_
    rw [hρ]; simp)
  have hl : lift x (lift y u) = ρ ≫ lift p₀ (lift p₁ p₂) := by
    rw [comp_lift, comp_lift, r₀, r₁, r₂]
  have hχ : ρ.left.appTop.hom (chi (X × X × X) (a, b, d)) =
      (toHom ρ (Multiplicative.ofAdd (a, b, d))).val := by
    conv_rhs => rw [← Category.comp_id ρ, toHom_comp_val]
    rfl
  rw [hl, ← over_appTop_comp, e, map_mul, hχ, hρ, ← appTop_comp_apply, Over.w]
  simp
end GlobalTheory.TorusCube
