-- Prove2me | solution 1 for GlobalTheory.GenericFibreSections.exists_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:00:26.626784+00:00
-- url     : https://prove2.me/submissions/ca1981e2-7a20-4972-8cb9-4452f8dd0755

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_BijectiveOfIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self


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
open GlobalTheory GlobalTheory.GenericFibreSections
variable {X₁ X₂ Y Y' : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂}
namespace GlobalTheory.GenericFibreSections
theorem _root_.solution (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (φ₁ : Y ⟶ X₁) (φ₂ : Y ⟶ X₂) (k : ℤ)
    (V : L₁.ι → L₂.ι → Y.Opens) (hV : ∀ i j y, φ₁ y ∈ L₁.U i → φ₂ y ∈ L₂.U j → y ∈ V i j)
    (u : ∀ i j, Γ(Y, V i j)ˣ)
    (hu : ∀ (y : Y) i i' j j', φ₁ y ∈ L₁.U i → φ₁ y ∈ L₁.U i' → φ₂ y ∈ L₂.U j → φ₂ y ∈ L₂.U j' →
      gm (𝟙 Y) y _ (u i j) * gm (𝟙 Y ≫ φ₁) y _ (L₁.g i i') ^ k =
        gm (𝟙 Y ≫ φ₂) y _ (L₂.g j j') ^ k * gm (𝟙 Y) y _ (u i' j'))
    (s : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => φ₁) (fun _ => k))) :
    ∃ s' : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => φ₂) (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J₁ J₂, Good L₁ z J₁ → Good L₂ z J₂ →
        sval s' r z J₂ = (gm r z _ (u (J₁ (r ≫ φ₁)) (J₂ (r ≫ φ₂)))).val * sval s r z J₁ := by
  have glue : ∀ j : Fin 1 → L₂.ι, ∃ a : Γ(Y, LB.wchart L₂ (fun _ : Fin 1 => φ₂) j),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L₁.ι),
      r z ∈ LB.wchart L₂ (fun _ : Fin 1 => φ₂) j → φ₁ (r z) ∈ L₁.U i →
      gs r z _ a = (gm r z _ (u i (j 0))).val *
        gs r z (LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i)) (s.f (fun _ => i)) := by
    intro j
    let W : L₁.ι → Y.Opens := fun i =>
      LB.wchart L₂ (fun _ : Fin 1 => φ₂) j ⊓ LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i)
    have l : ∀ i, W i ≤ V i (j 0) := fun i y hy =>
      hV i (j 0) y (Set.mem_iInter.1 hy.2 0) (Set.mem_iInter.1 hy.1 0)
    obtain ⟨b, hb⟩ : ∃ b : ∀ i, Γ(Y, W i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) i, r z ∈ W i →
        gs r z (W i) (b i) = (gm r z _ (u i (j 0))).val *
          gs r z (LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i)) (s.f (fun _ => i)) :=
      ⟨fun i => (Y.presheaf.map (homOfLE (l i)).op).hom (u i (j 0)).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W i ≤ LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i))).op).hom
            (s.f (fun _ => i)), fun Z r z i hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans (gs_unit r z _ (l i hz) _))
          (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L₂ (fun _ : Fin 1 => φ₂) j)
      (fun i => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨i, hi⟩ := exists_chart hL₁ (φ₁ y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy, Set.mem_iInter.2 fun _ => hi⟩) b
      (fun i i' => fn_ext (V := W i ⊓ W i') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        have m : φ₂ y ∈ L₂.U (j 0) := Set.mem_iInter.1 hy.1.1 0
        have e := hu y i i' (j 0) (j 0) (Set.mem_iInter.1 hy.1.2 0) (Set.mem_iInter.1 hy.2.2 0) m m
        rw [gm_self hL₂ (𝟙 Y ≫ φ₂) y m, _root_.one_zpow, _root_.one_mul] at e
        rw [hb _ _ y i hy.1, hb _ _ y i' hy.2, sec_trans s (𝟙 Y) y hy.1.2 hy.2.2, ← _root_.mul_assoc, ← Units.val_mul,
          ← e, trF, Fintype.prod_unique])
    refine ⟨a, fun Z r z i h₁ h₂ => ?_⟩
    have hz : r z ∈ W i := ⟨h₁, Set.mem_iInter.2 fun _ => h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z (W i)) (ha i)).trans (hb Z r z i hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart hL₁ (φ₁ y)
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L₂ _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    refine (ha j _ (𝟙 Y) y i hy.1 hi).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 Y) y i hy.2 hi)).symm)
    have e := hu y i i (j 0) (j' 0) hi hi (Set.mem_iInter.1 hy.1 0) (Set.mem_iInter.1 hy.2 0)
    rw [gm_self hL₁ (𝟙 Y ≫ φ₁) y hi, _root_.one_zpow, _root_.mul_one] at e
    rw [e, Fintype.prod_unique, Units.val_mul, _root_.mul_assoc]
    rfl
  · exact ha _ Z r z (J₁ (r ≫ φ₁)) (hJ₂.mem (fun _ : Fin 1 => φ₂) r) (hJ₁ (r ≫ φ₁))
end GlobalTheory.GenericFibreSections
