-- Prove2me | solution 1 for GlobalTheory.WtBundle.exists_gen_desc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:13:41.042565+00:00
-- url     : https://prove2.me/submissions/f6d784f1-9948-4c3f-927d-591a336c2b4a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CommGroupCommonFactorQuotientCancel
import Theorems.Thm_GlobalTheory_WtBundle_unit_ext_of_flat
import Theorems.Thm_GlobalTheory_WtBundle_exists_unit_desc
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.WtBundle
variable {X Y Z W : Scheme.{0}}
namespace GlobalTheory.WtBundle
theorem _root_.solution {G B Y' : Scheme.{0}} (q : G ⟶ B) (N : LB B) (u : ∀ j, Γ(G, q ⁻¹ᵁ N.U j)ˣ)
    (hu : ∀ (Z : Scheme.{0}) (g : Z ⟶ G) (z : Z) (i j : N.ι), q (g z) ∈ N.U i → q (g z) ∈ N.U j →
      gm g z (q ⁻¹ᵁ N.U i) (u i) = gm (g ≫ q) z (N.U i ⊓ N.U j) (N.g i j) * gm g z (q ⁻¹ᵁ N.U j) (u j))
    (π : Y' ⟶ Y) [Flat π] [Surjective π] [QuasiCompact π] {K : Type} [Fintype K] (φ : K → (Y ⟶ B))
    (ψ : K → (Y' ⟶ G)) (hψ : ∀ k, ψ k ≫ q = π ≫ φ k) (ε : K → ℤ)
    (inv : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ Y') (z : Z) (j : K → N.ι), g₁ ≫ π = g₂ ≫ π →
      (∀ k, q ((g₂ ≫ ψ k) z) ∈ N.U (j k)) →
      ∏ k, gm (g₁ ≫ ψ k) z (q ⁻¹ᵁ N.U (j k)) (u (j k)) ^ ε k =
        ∏ k, gm (g₂ ≫ ψ k) z (q ⁻¹ᵁ N.U (j k)) (u (j k)) ^ ε k) :
    ∃ s : LB.Gen (LB.LinComb N φ ε), s.IsGen := by
  have le : ∀ (j : K → N.ι) k, π ⁻¹ᵁ LB.wchart N φ j ≤ ψ k ⁻¹ᵁ (q ⁻¹ᵁ N.U (j k)) := fun j k y hy =>
    (congrArg (fun m : Y' ⟶ B => m y ∈ N.U (j k)) (hψ k)).mpr (Set.mem_iInter.1 hy k)
  have loc : ∀ j : K → N.ι, ∃ a : Γ(Y, LB.wchart N φ j)ˣ, ∀ (Z : Scheme.{0}) (g : Z ⟶ Y') (z : Z),
      π (g z) ∈ LB.wchart N φ j → gm (g ≫ π) z (LB.wchart N φ j) a =
        ∏ k, gm (g ≫ ψ k) z (q ⁻¹ᵁ N.U (j k)) (u (j k)) ^ ε k := fun j => by
    have v : ∀ (Z : Scheme.{0}) (g : Z ⟶ Y') (z : Z), π (g z) ∈ LB.wchart N φ j →
        gm g z (π ⁻¹ᵁ LB.wchart N φ j) (∏ k, res (le j k) (pullU (ψ k) _ (u (j k))) ^ ε k) =
          ∏ k, gm (g ≫ ψ k) z (q ⁻¹ᵁ N.U (j k)) (u (j k)) ^ ε k := fun Z g z hz => by
      rw [map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [map_zpow, gm_res g z (le j k) hz, gm_pull g (ψ k) z _ (le j k hz)]
    obtain ⟨a, ha⟩ := exists_unit_desc π (LB.wchart N φ j) (∏ k, res (le j k) (pullU (ψ k) _ (u (j k))) ^ ε k)
      fun Z g₁ g₂ z e h₁ h₂ => by
        rw [v Z g₁ z h₁, v Z g₂ z h₂]
        exact inv Z g₁ g₂ z j e fun k => le j k h₂
    exact ⟨a, fun Z g z hz => (ha Z g z hz).trans (v Z g z hz)⟩
  choose a ha using loc
  refine ⟨⟨a⟩, fun j j' => unit_ext_of_flat π fun y hy => ?_⟩
  have b : ∀ j, π y ∈ LB.wchart N φ j → gm π y (LB.wchart N φ j) (a j) =
      ∏ k, gm (ψ k) y (q ⁻¹ᵁ N.U (j k)) (u (j k)) ^ ε k := fun j hj => by
    have := ha j _ (𝟙 Y') y hj
    simpa only [Category.id_comp] using this
  refine ((gm_res π y _ hy _).trans (b j hy.1)).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_linComb N φ ε π y j j' hy.1 hy.2) ((gm_res π y _ hy _).trans (b j' hy.2))).trans ?_)))
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← mul_zpow, hu _ (ψ k) y (j k) (j' k) (le j k hy.1) (le j' k hy.2), hψ]
end GlobalTheory.WtBundle
