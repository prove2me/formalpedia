-- Prove2me | solution 1 for GlobalTheory.GenDescent.exists_gen_of_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:10.114011+00:00
-- url     : https://prove2.me/submissions/bab4dbd0-7311-4dfa-bfda-b52ac38ea7ec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfQuotientOfRigid
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__e27165827f88
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullU_res__268497da66fb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_id_pull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor


section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
namespace GlobalTheory
namespace GenDescent
variable {Y Y' Z : Scheme.{0}}
private theorem gm_res' {X W : Scheme.{0}} (k : W ⟶ X) (w : W) {V V' : X.Opens} (h : V' ≤ V)
    (u : Γ(X, V)ˣ) (hw : k w ∈ V') : gm k w V' (res h u) = gm k w V u := by
  rw [← gm_id_pull k w V' hw (res h u), pullU_res₂, gm_rp₁ k w V _ _ hw]
private theorem units_eq_of_gm_id_eq {Y : Scheme.{0}} {V : Y.Opens} (u v : Γ(Y, V)ˣ)
    (h : ∀ y, y ∈ V → gm (𝟙 Y) y V u = gm (𝟙 Y) y V v) : u = v := by
  apply Units.ext
  apply TopCat.Presheaf.section_ext Y.sheaf V
  intro y hy
  have e := congrArg Units.val (h y hy)
  have hy' : (𝟙 Y) y ∈ V := hy
  simp only [gm, dif_pos hy', pullU, MonoidHom.comp_apply, Units.coe_map] at e
  exact e
end GenDescent
end GlobalTheory
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.GenDescent
variable {Y Y' Z : Scheme.{0}}
namespace GlobalTheory.GenDescent
theorem _root_.solution {N : LB Z} {f : Y ⟶ Z} {a} (ha : Compat N f a)
    (hinj : ∀ V, Function.Injective (f.app V).hom)
    (h₁ : ∀ i, (a i).val ∈ Set.range (f.app (N.U i)).hom)
    (h₂ : ∀ i, ((a i)⁻¹).val ∈ Set.range (f.app (N.U i)).hom) :
    ∃ t : N.Gen, t.IsGen := by
  choose b hb using h₁
  choose c hc using h₂
  have hbc : ∀ i, b i * c i = 1 := fun i => hinj _ (by rw [map_mul, hb, hc, map_one]; exact (a i).mul_inv)
  refine ⟨⟨fun i => ⟨b i, c i, hbc i, (mul_comm _ _).trans (hbc i)⟩⟩, ?_⟩
  unfold LB.Gen.IsGen
  intro i j
  have key : res (f.preimage_mono (inf_le_left : N.U i ⊓ N.U j ≤ N.U i)) (a i) =
      pullU f _ (N.g i j) * res (f.preimage_mono (inf_le_right : N.U i ⊓ N.U j ≤ N.U j)) (a j) := by
    refine units_eq_of_gm_id_eq _ _ fun y hy => ?_
    rw [map_mul, gm_res' _ _ _ _ hy, gm_res' _ _ _ _ hy, gm_pullU_eq_gm_comp]
    exact ha Y (𝟙 Y) y i j hy.1 hy.2
  apply Units.ext
  apply hinj
  have e := congrArg Units.val key
  simp only [res, pullU, Units.coe_map, Units.val_mul, MonoidHom.coe_coe] at e ⊢
  have nat : ∀ (V V' : Z.Opens) (h : V' ≤ V) (x : Γ(Z, V)),
      (f.app V').hom ((Z.presheaf.map (homOfLE h).op).hom x) =
        (Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom ((f.app V).hom x) := by
    intro V V' h x
    show (Z.presheaf.map (homOfLE h).op ≫ f.app V').hom x = (f.app V ≫ Y.presheaf.map _).hom x
    rw [Scheme.Hom.naturality]
    rfl
  rw [nat, map_mul, nat, hb, hb]
  exact e
end GlobalTheory.GenDescent
