-- Prove2me | solution 1 for GlobalTheory.UU.PullSec.exists_sec_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:16:05.869044+00:00
-- url     : https://prove2.me/submissions/9526d82c-7dec-42f6-a52b-81f179eaeee2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniquePullB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.PullSec
variable {X X' W Y Y₂ : Scheme.{0}}
namespace GlobalTheory.UU.PullSec
theorem _root_.solution {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) {F : W ⟶ X} {F' : W ⟶ X'}
    (w : LB.Iso (L'.pull F') (L.pull F)) (hw : w.IsGen) (y₀ : Y ⟶ W) (h : Y ⟶ Y₂) (a : Y ⟶ X') (b : Y₂ ⟶ X)
    (ha : y₀ ≫ F' = a) (hb : y₀ ≫ F = h ≫ b) (k : ℕ)
    (σ : LB.Sec (LB.LinComb L (fun _ : Fin 1 => b) (fun _ => (k : ℤ)))) :
    ∃ t : LB.Sec (LB.LinComb L' (fun _ : Fin 1 => a) (fun _ => (k : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L.ι) (j : L'.ι), F (y₀ (r z)) ∈ L.U i → F' (y₀ (r z)) ∈ L'.U j →
        (gw w (r ≫ y₀) z i (fun _ => j)).val ^ k *
            gs r z (LB.wchart L' (fun _ : Fin 1 => a) (fun _ => j)) (t.f fun _ => j) =
          gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i)) (σ.f fun _ => i) := by
  subst ha
  have pw := (isGen_iff w).1 hw
  have pt : ∀ y : Y, b (h y) = F (y₀ y) := fun y => congrArg (fun g => g y) hb.symm
  have mb : ∀ (y : Y) (i : L.ι), F (y₀ y) ∈ L.U i → h y ∈ LB.wchart L (fun _ : Fin 1 => b) (fun _ => i) :=
    fun y i hi => Set.mem_iInter.2 fun _ => show b (h y) ∈ L.U i by rw [pt]; exact hi
  have tw : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i i' : L.ι) (j j' : L'.ι), F (y₀ (r z)) ∈ L.U i →
      F (y₀ (r z)) ∈ L.U i' → F' (y₀ (r z)) ∈ L'.U j → F' (y₀ (r z)) ∈ L'.U j' →
      ((gw w (r ≫ y₀) z i (fun _ => j))⁻¹ ^ k).val *
          gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i)) (σ.f fun _ => i) =
        (gm (r ≫ y₀ ≫ F') z (L'.U j ⊓ L'.U j') (L'.g j j') ^ (k : ℤ)).val *
          (((gw w (r ≫ y₀) z i' (fun _ => j'))⁻¹ ^ k).val *
            gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i')) (σ.f fun _ => i')) := by
    intro Z r z i i' j j' hi hi' hj hj'
    have e := pw Z (r ≫ y₀) z i i' (fun _ => j) (fun _ => j') hi hi' (mem_pull.2 hj) (mem_pull.2 hj')
    rw [gm_pull_g L' F' (r ≫ y₀) z (fun _ => j) (fun _ => j') (mem_pull.2 hj) (mem_pull.2 hj')] at e
    rw [sec_trans σ (r ≫ h) z (mb _ i hi) (mb _ i' hi'), trF, Fintype.prod_unique, e, ← _root_.mul_assoc,
      ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
    congr 2
    rw [Category.assoc r h b, ← hb, Category.assoc r y₀ F, Category.assoc r y₀ F', zpow_natCast, zpow_natCast,
      ← mul_pow, ← mul_pow]
    congr 1
    generalize gm (r ≫ y₀ ≫ F) z (L.U i ⊓ L.U i') (L.g i i') = P
    generalize gm (r ≫ y₀ ≫ F') z (L'.U j ⊓ L'.U j') (L'.g j j') = Q
    generalize gw w (r ≫ y₀) z i' (fun _ => j') = C
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have glue : ∀ j : Fin 1 → L'.ι, ∃ s : Γ(Y, LB.wchart L' (fun _ : Fin 1 => y₀ ≫ F') j),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L.ι), F (y₀ (r z)) ∈ L.U i → F' (y₀ (r z)) ∈ L'.U (j 0) →
        gs r z _ s = ((gw w (r ≫ y₀) z i (fun _ => j 0))⁻¹ ^ k).val *
          gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i)) (σ.f fun _ => i) := by
    intro j
    obtain ⟨V, hV⟩ : ∃ V : L.ι → Y.Opens, ∀ i y, y ∈ V i ↔ F (y₀ y) ∈ L.U i ∧ F' (y₀ y) ∈ L'.U (j 0) :=
      ⟨fun i => y₀ ⁻¹ᵁ (F ⁻¹ᵁ L.U i) ⊓ y₀ ⁻¹ᵁ (F' ⁻¹ᵁ L'.U (j 0)), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ i, V i ≤ LB.wchart L' (fun _ : Fin 1 => y₀ ≫ F') j := fun i y hy =>
      Set.mem_iInter.2 fun c => by rw [Subsingleton.elim c 0]; exact ((hV i y).1 hy).2
    have l₁ : ∀ i, V i ≤ y₀ ⁻¹ᵁ ((L.pull F).U (fun _ => i) ⊓ (L'.pull F').U (fun _ => j 0)) := fun i y hy =>
      ⟨mem_pull.2 ((hV i y).1 hy).1, mem_pull.2 ((hV i y).1 hy).2⟩
    have l₂ : ∀ i, V i ≤ h ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => b) (fun _ => i) := fun i y hy =>
      mb y i ((hV i y).1 hy).1
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(Y, V i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L.ι), r z ∈ V i →
        gs r z (V i) (u i) = ((gw w (r ≫ y₀) z i (fun _ => j 0))⁻¹ ^ k).val *
          gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i)) (σ.f fun _ => i) :=
      ⟨fun i => ((res (l₁ i) (pullU y₀ _ (w.s (fun _ => i, fun _ => j 0))))⁻¹ ^ k).val *
          (Y.presheaf.map (homOfLE (l₂ i)).op).hom ((h.app _).hom (σ.f fun _ => i)), fun Z r z i hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hz _).trans (congrArg Units.val
          ((map_pow _ _ _).trans (congrArg (· ^ k) ((map_inv _ _).trans (congrArg (·⁻¹)
            ((gm_res r z (l₁ i) hz _).trans (gm_pull r y₀ z _ (l₁ i hz) _))))))))
          ((gs_res r z (l₂ i) hz _).trans (gs_pull r h z _ (l₂ i hz) _)))⟩
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' V (LB.wchart L' (fun _ : Fin 1 => y₀ ≫ F') j)
      (fun i => homOfLE (l₀ i)) (fun y hy => by
        obtain ⟨i, hi⟩ := exists_chart hL (F (y₀ y))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hV i y).2 ⟨hi, Set.mem_iInter.1 hy 0⟩⟩) u
      (fun i i' => fn_ext (V := V i ⊓ V i') fun y hy => by
        have h₁ := (hV i y).1 hy.1
        have h₂ := (hV i' y).1 hy.2
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hu _ _ y i hy.1, hu _ _ y i' hy.2, tw _ (𝟙 Y) y i i' (j 0) (j 0) h₁.1 h₂.1 h₁.2 h₁.2,
          gm_self hL' (𝟙 Y ≫ y₀ ≫ F') y h₁.2, one_zpow, Units.val_one, _root_.one_mul])
    refine ⟨s, fun Z r z i h₁ h₂ => ?_⟩
    have hz : r z ∈ V i := (hV i _).2 ⟨h₁, h₂⟩
    exact (gs_res r z (l₀ i) hz s).symm.trans ((congrArg (gs r z (V i)) (hs i)).trans (hu Z r z i hz))
  choose s hs using glue
  refine ⟨⟨s, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z i j hi hj => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart hL (F (y₀ y))
    have m : F' (y₀ y) ∈ L'.U (j 0) := Set.mem_iInter.1 hy.1 0
    have m' : F' (y₀ y) ∈ L'.U (j' 0) := Set.mem_iInter.1 hy.2 0
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L' _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    refine (hs j _ (𝟙 Y) y i hi m).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y i hi m')).symm)
    rw [Fin.prod_univ_one]
    exact tw _ (𝟙 Y) y i i (j 0) (j' 0) hi hi m m'
  · refine (congrArg _ (hs (fun _ => j) Z r z i hi hj)).trans ?_
    rw [← _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow,
      Units.val_one, _root_.one_mul]
end GlobalTheory.UU.PullSec
