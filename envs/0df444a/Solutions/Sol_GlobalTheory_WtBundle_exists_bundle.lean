-- Prove2me | solution 1 for GlobalTheory.WtBundle.exists_bundle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:09:42.681801+00:00
-- url     : https://prove2.me/submissions/5df0f6b4-691a-49c8-8ae8-0d00e616b99a

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
import Theorems.Thm_GlobalTheory_WtBundle_commGroup_common_factor_quotient_cancel
import Theorems.Thm_GlobalTheory_WtBundle_exists_act
import Theorems.Thm_GlobalTheory_WtBundle_gm_act
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
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
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.WtBundle
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]
variable (Q : TQ G X)
namespace GlobalTheory.WtBundle
theorem _root_.solution (χ : X) : ∃ (N : LB Q.B.left) (u : ∀ j, Γ(G.left, Q.q.left ⁻¹ᵁ N.U j)ˣ), N.IsLB ∧
    (∀ j, IsWt Q.i _ (u j).val χ) ∧
    ∀ (Z : Scheme.{0}) (g : Z ⟶ G.left) (z : Z) (i j : N.ι), Q.q.left (g z) ∈ N.U i → Q.q.left (g z) ∈ N.U j →
      gm g z (Q.q.left ⁻¹ᵁ N.U i) (u i) =
        gm (g ≫ Q.q.left) z (N.U i ⊓ N.U j) (N.g i j) * gm g z (Q.q.left ⁻¹ᵁ N.U j) (u j) := by
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  choose V hV u hu using fun b => Q.loc b χ
  have tr : ∀ i j, ∃ a : Γ(Q.B.left, V i ⊓ V j)ˣ, ∀ (Z : Scheme.{0}) (g : Z ⟶ G.left) (z : Z),
      Q.q.left (g z) ∈ V i → Q.q.left (g z) ∈ V j → gm (g ≫ Q.q.left) z (V i ⊓ V j) a =
        gm g z (Q.q.left ⁻¹ᵁ V i) (u i) * (gm g z (Q.q.left ⁻¹ᵁ V j) (u j))⁻¹ := fun i j => by
    have l₁ : Q.q.left ⁻¹ᵁ (V i ⊓ V j) ≤ Q.q.left ⁻¹ᵁ V i := fun _ h => h.1
    have l₂ : Q.q.left ⁻¹ᵁ (V i ⊓ V j) ≤ Q.q.left ⁻¹ᵁ V j := fun _ h => h.2
    have v : ∀ (Z : Scheme.{0}) (g : Z ⟶ G.left) (z : Z), Q.q.left (g z) ∈ V i ⊓ V j →
        gm g z (Q.q.left ⁻¹ᵁ (V i ⊓ V j)) (res l₁ (u i) * (res l₂ (u j))⁻¹) =
          gm g z (Q.q.left ⁻¹ᵁ V i) (u i) * (gm g z (Q.q.left ⁻¹ᵁ V j) (u j))⁻¹ := fun Z g z hz => by
      rw [map_mul, map_inv, gm_res g z l₁ hz, gm_res g z l₂ hz]
    obtain ⟨a, ha⟩ := exists_unit_desc Q.q.left (V i ⊓ V j) (res l₁ (u i) * (res l₂ (u j))⁻¹)
      fun Z g₁ g₂ z e h₁ h₂ => by
        let Z' : Over S := Over.mk (g₂ ≫ G.hom)
        let k₂ : Z' ⟶ G := Over.homMk g₂ rfl
        let k₁ : Z' ⟶ G := Over.homMk g₁ (by
          change g₁ ≫ G.hom = g₂ ≫ G.hom
          rw [← Over.w Q.q, reassoc_of% e])
        obtain ⟨t, ht⟩ := exists_act Q (show k₁ ≫ Q.q = k₂ ≫ Q.q from Over.OverMorphism.ext e)
        have a₁ := gm_act Q (hu i) t k₂ z h₂.1
        have a₂ := gm_act Q (hu j) t k₂ z h₂.2
        rw [← ht] at a₁ a₂
        rw [v Z g₁ z h₁, v Z g₂ z h₂]
        exact (congrArg₂ (fun a b => a * b⁻¹) a₁ a₂).trans (commGroup_common_factor_quotient_cancel _ _ _)
    exact ⟨a, fun Z g z h₁ h₂ => (ha Z g z ⟨h₁, h₂⟩).trans (v Z g z ⟨h₁, h₂⟩)⟩
  choose a ha using tr
  have b : ∀ i j x, Q.q.left x ∈ V i → Q.q.left x ∈ V j → gm Q.q.left x (V i ⊓ V j) (a i j) =
      gm (𝟙 _) x (Q.q.left ⁻¹ᵁ V i) (u i) * (gm (𝟙 _) x (Q.q.left ⁻¹ᵁ V j) (u j))⁻¹ := fun i j x h₁ h₂ => by
    have := ha i j _ (𝟙 _) x h₁ h₂
    rwa [Category.id_comp] at this
  refine ⟨⟨_, V, a⟩, u, ⟨?_, fun i => ?_, fun i j k => ?_⟩, hu, fun Z g z i j h₁ h₂ => ?_⟩
  · exact top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hV x⟩
  · refine unit_ext_of_flat Q.q.left fun x hx => ?_
    exact (gm_res _ x _ hx _).trans ((b i i x hx hx).trans ((mul_inv_cancel _).trans (map_one _).symm))
  · refine unit_ext_of_flat Q.q.left fun x hx => ?_
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ x _ hx _).trans (b i j x hx.1.1 hx.1.2))
      ((gm_res _ x _ hx _).trans (b j k x hx.1.2 hx.2)))).trans
      (Eq.trans ?_ ((gm_res _ x _ hx _).trans (b i k x hx.1.1 hx.2)).symm)
    rw [_root_.mul_assoc, inv_mul_cancel_left]
  · exact eq_mul_of_mul_inv_eq (ha i j Z g z h₁ h₂).symm
end GlobalTheory.WtBundle
