-- Prove2me | solution 1 for GlobalTheory.WtBundle.exists_gen_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:27:50.656059+00:00
-- url     : https://prove2.me/submissions/53a73db9-dea4-4155-ac8f-6a54c81043fb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CommGroupCommonFactorQuotientCancel
import Theorems.Thm_GlobalTheory_WtBundle_exists_gen_desc
import Theorems.Thm_GlobalTheory_WtBundle_exists_act
import Theorems.Thm_GlobalTheory_WtBundle_gm_act
import Theorems.Thm_GlobalTheory_WtBundle_comp_sq
import Theorems.Thm_GlobalTheory_WtBundle_sq_comp
import Theorems.Thm_GlobalTheory_WtBundle_sq_mul
import Theorems.Thm_GlobalTheory_WtBundle_prod_sq
import Theorems.Thm_GlobalTheory_WtBundle_prod_psum
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen


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
variable {S : Scheme.{0}}
variable {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X] (Q : TQ G X)
namespace GlobalTheory.WtBundle
theorem _root_.solution (χ : X) (N : LB Q.B.left) (hN : N.IsLB) (u : ∀ j, Γ(G.left, Q.q.left ⁻¹ᵁ N.U j)ˣ)
    (hw : ∀ j, IsWt Q.i _ (u j).val χ)
    (hu : ∀ (Z : Scheme.{0}) (g : Z ⟶ G.left) (z : Z) (i j : N.ι), Q.q.left (g z) ∈ N.U i → Q.q.left (g z) ∈ N.U j →
      gm g z (Q.q.left ⁻¹ᵁ N.U i) (u i) =
        gm (g ≫ Q.q.left) z (N.U i ⊓ N.U j) (N.g i j) * gm g z (Q.q.left ⁻¹ᵁ N.U j) (u j)) :
    ∃ s : LB.Gen (abelian₂ Q.B N), s.IsGen := by
  have := Q.q_hom
  have := Q.i_hom
  have := Q.q_affine
  have : Flat (Q.q ⊗ₘ Q.q).left := MorphismProperty.pullbackMap (P := @Flat) Q.q_flat Q.q_flat
    (Over.w Q.q).symm (Over.w Q.q).symm
  have : MorphismProperty.IsStableUnderComposition @Surjective := ⟨fun f g _ _ => inferInstance⟩
  have : Surjective (Q.q ⊗ₘ Q.q).left := MorphismProperty.pullbackMap (P := @Surjective) Q.q_surj Q.q_surj
    (Over.w Q.q).symm (Over.w Q.q).symm
  have : QuasiCompact (Q.q ⊗ₘ Q.q).left := MorphismProperty.pullbackMap (P := @QuasiCompact)
    (inferInstanceAs (QuasiCompact Q.q.left)) (inferInstanceAs (QuasiCompact Q.q.left))
    (Over.w Q.q).symm (Over.w Q.q).symm
  obtain ⟨s, hs⟩ := exists_gen_desc Q.q.left N u hu (Q.q ⊗ₘ Q.q).left
    (fun k => (sq (fst Q.B Q.B) (snd Q.B Q.B) k).left) (fun k => (sq (fst G G) (snd G G) k).left)
    (fun k => by
      rw [← Over.comp_left, ← Over.comp_left, sq_comp, comp_sq, tensorHom_fst, tensorHom_snd]) Oε
    fun Z g₁ g₂ z j e h₂ => by
      let Z' : Over S := Over.mk (g₂ ≫ (G ⊗ G).hom)
      let k₂ : Z' ⟶ G ⊗ G := Over.homMk g₂ rfl
      let k₁ : Z' ⟶ G ⊗ G := Over.homMk g₁ (by
        change g₁ ≫ (G ⊗ G).hom = g₂ ≫ (G ⊗ G).hom
        rw [← Over.w (Q.q ⊗ₘ Q.q), reassoc_of% e])
      have e' : k₁ ≫ (Q.q ⊗ₘ Q.q) = k₂ ≫ (Q.q ⊗ₘ Q.q) := Over.OverMorphism.ext e
      obtain ⟨t, ht⟩ := exists_act Q (a := k₁ ≫ fst G G) (b := k₂ ≫ fst G G) (by
        rw [Category.assoc, Category.assoc, ← tensorHom_fst Q.q Q.q, reassoc_of% e'])
      obtain ⟨t', ht'⟩ := exists_act Q (a := k₁ ≫ snd G G) (b := k₂ ≫ snd G G) (by
        rw [Category.assoc, Category.assoc, ← tensorHom_snd Q.q Q.q, reassoc_of% e'])
      have a : ∀ k, k₁ ≫ sq (fst G G) (snd G G) k = (sq t t' k ≫ Q.i) * (k₂ ≫ sq (fst G G) (snd G G) k) :=
        fun k => by rw [comp_sq, comp_sq, ht, ht', sq_mul, sq_comp]
      have b : ∀ k, gm (k₁ ≫ sq (fst G G) (snd G G) k).left z (Q.q.left ⁻¹ᵁ N.U (j k)) (u (j k)) =
          gm (𝟙 Z'.left) z ⊤ (chV (sq t t' k) χ) *
            gm (k₂ ≫ sq (fst G G) (snd G G) k).left z (Q.q.left ⁻¹ᵁ N.U (j k)) (u (j k)) := fun k => by
        rw [a]; exact gm_act Q (hw (j k)) (sq t t' k) (k₂ ≫ sq (fst G G) (snd G G) k) z (h₂ k)
      have c : ∏ k, gm (𝟙 Z'.left) z ⊤ (chV (sq t t' k) χ) ^ Oε k = 1 := by
        have o : chV (1 : Z' ⟶ splitTorus S X) χ = 1 := by rw [chV, map_one]; rfl
        rw [prod_sq t t' fun a => gm (𝟙 Z'.left) z ⊤ (chV a χ), chV_mul, o, map_mul, map_one, _root_.mul_one,
          mul_right_comm, mul_inv_cancel_right, mul_inv_cancel]
      refine (Finset.prod_congr rfl fun k _ => (congrArg (· ^ Oε k) (b k)).trans (mul_zpow _ _ _)).trans ?_
      exact Finset.prod_mul_distrib.trans ((congrArg (· * _) c).trans (_root_.one_mul _))
  obtain ⟨s', hs', -⟩ := exists_gen hN (K' := ULift.{0} (Finset (Fin 2)))
    (φ' := fun I => (psum Q.B (x2 Q.B) I.down).left) (ε' := fun I => (-1) ^ (2 - I.down.card))
    (fun U _ h => (prod_sq _ _ fun a => h a.left).trans (prod_psum (x2 Q.B) fun a => h a.left).symm) s hs
  exact ⟨s', hs'⟩
end GlobalTheory.WtBundle
