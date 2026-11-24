-- Prove2me | solution 1 for GlobalTheory.GenDescent.Compat.ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:58:53.805032+00:00
-- url     : https://prove2.me/submissions/017aec76-352c-4953-8bf4-9ba56b45ca39

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
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
private theorem gm_id_val_eq_germ' {Y : Scheme.{0}} {V : Y.Opens} (u : Γ(Y, V)ˣ) (y : Y) (hy : y ∈ V) :
    (gm (𝟙 Y) y V u).val = Y.presheaf.germ V y hy u.val := by
  have hy' : (𝟙 Y) y ∈ V := hy
  simp only [gm, dif_pos hy', pullU, MonoidHom.comp_apply, Units.coe_map]
  rfl
private theorem exists_global_unit_of_gm_agree_on_cover {Y : Scheme.{0}} {I : Type} (V : I → Y.Opens) (hcov : ⊤ ≤ ⨆ i, V i)
    (d : ∀ i, Γ(Y, V i)ˣ)
    (hd : ∀ y i j, y ∈ V i → y ∈ V j → gm (𝟙 Y) y (V i) (d i) = gm (𝟙 Y) y (V j) (d j)) :
    ∃ c : Γ(Y, ⊤)ˣ, ∀ i, res (le_top : V i ≤ ⊤) c = d i := by
  have comp : ∀ s : ∀ i, Γ(Y, V i)ˣ, (∀ y i j, y ∈ V i → y ∈ V j →
      gm (𝟙 Y) y (V i) (s i) = gm (𝟙 Y) y (V j) (s j)) →
      TopCat.Presheaf.IsCompatible Y.sheaf.1 V (fun i => (s i).val) := by
    intro s hs i j
    apply TopCat.Presheaf.section_ext Y.sheaf (V i ⊓ V j)
    intro y hy
    have e := congrArg Units.val (hs y i j hy.1 hy.2)
    rw [gm_id_val_eq_germ' _ y hy.1, gm_id_val_eq_germ' _ y hy.2] at e
    have e₁ := Y.presheaf.germ_res_apply (TopologicalSpace.Opens.infLELeft (V i) (V j)) y hy (s i).val
    have e₂ := Y.presheaf.germ_res_apply (TopologicalSpace.Opens.infLERight (V i) (V j)) y hy (s j).val
    exact e₁.trans (e.trans e₂.symm)
  obtain ⟨c₁, hc₁, -⟩ := Y.sheaf.existsUnique_gluing' V ⊤ (fun i => homOfLE le_top) hcov
    (fun i => (d i).val) (comp d hd)
  obtain ⟨c₂, hc₂, -⟩ := Y.sheaf.existsUnique_gluing' V ⊤ (fun i => homOfLE le_top) hcov
    (fun i => (d i)⁻¹.val) (comp (fun i => (d i)⁻¹) fun y i j hi hj => by
      rw [map_inv, map_inv, hd y i j hi hj])
  have h₁₂ : c₁ * c₂ = 1 := by
    apply Y.sheaf.eq_of_locally_eq' V ⊤ (fun i => homOfLE le_top) hcov
    intro i
    rw [map_mul, map_one, hc₁ i, hc₂ i]
    exact (d i).mul_inv
  refine ⟨⟨c₁, c₂, h₁₂, (mul_comm _ _).trans h₁₂⟩, fun i => Units.ext ?_⟩
  exact hc₁ i
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
namespace Compat
theorem _root_.solution {N : LB Z} (hN : N.IsLB) {f : Y ⟶ Z} {a b} (ha : Compat N f a)
    (hb : Compat N f b) :
    ∃ c : Γ(Y, ⊤)ˣ, ∀ (W : Scheme.{0}) (k : W ⟶ Y) (w : W) (i : N.ι), f (k w) ∈ N.U i →
      gm k w _ (a i) = gm k w ⊤ c * gm k w _ (b i) := by
  obtain ⟨hcov, -, -⟩ := hN
  have hcovY : (⊤ : Y.Opens) ≤ ⨆ i, f ⁻¹ᵁ N.U i := fun x _ => by
    have hx : f x ∈ ⨆ i, N.U i := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨c, hc⟩ := exists_global_unit_of_gm_agree_on_cover (fun i => f ⁻¹ᵁ N.U i) hcovY (fun i => a i * (b i)⁻¹)
    fun y i j hi hj => by
      rw [map_mul, map_mul, map_inv, map_inv, ha Y (𝟙 Y) y i j hi hj, hb Y (𝟙 Y) y i j hi hj,
        ← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
  refine ⟨c, fun W k w i hi => ?_⟩
  rw [← gm_res' k w (le_top : f ⁻¹ᵁ N.U i ≤ ⊤) c hi, hc i, map_mul, map_inv, inv_mul_cancel_right]
end Compat
end GlobalTheory.GenDescent
