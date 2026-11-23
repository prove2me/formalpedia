-- Prove2me | solution 1 for GlobalTheory.SecPullIso.exists_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:11.817769+00:00
-- url     : https://prove2.me/submissions/a3f0d29a-ad3f-432b-9363-ab2b1a453859

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionPull
import Theorems.Thm_GlobalTheory_SecPullIso_gs_sec_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SecPullIso
namespace GlobalTheory.SecPullIso
theorem _root_.solution {X X' : Scheme.{0}} (φ : X' ⟶ X) (H : LB X) (H' : LB X') (w : LB.Iso H' (H.pull φ))
    (hH : H.IsLB) (hH' : H'.IsLB) (hw : w.IsGen) (s : LB.Sec H) :
    ∃ s' : LB.Sec H', ∀ z (k : H.ι) (k' : H'.ι), φ z ∈ H.U k → z ∈ H'.U k' →
      gs φ z _ (s.f k) = (Geo.Tor.gw w (𝟙 _) z k k').val * gs (𝟙 _) z _ (s'.f k') := by
  have hp := (isGen_iff w).1 hw
  have ind : ∀ (z : X') (k j : H.ι) (k' j' : H'.ι), φ z ∈ H.U k → φ z ∈ H.U j → z ∈ H'.U k' → z ∈ H'.U j' →
      ((Geo.Tor.gw w (𝟙 _) z k k')⁻¹).val * gs φ z _ (s.f k) =
        (gm (𝟙 X') z _ (H'.g k' j')).val * (((Geo.Tor.gw w (𝟙 _) z j j')⁻¹).val * gs φ z _ (s.f j)) := by
    intro z k j k' j' hk hj hk' hj'
    have a := hp _ (𝟙 X') z k j k' j' hk hj hk' hj'
    rw [Category.id_comp] at a
    rw [a, gs_sec_trans s φ z hk hj, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
    generalize gm φ z _ (H.g k j) = A
    generalize gm (𝟙 X') z _ (H'.g k' j') = B
    generalize Geo.Tor.gw w (𝟙 _) z j j' = C
    congr 2
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have glue : ∀ k' : H'.ι, ∃ a : Γ(X', H'.U k'), ∀ (z : X') (k : H.ι), φ z ∈ H.U k → z ∈ H'.U k' →
      gs (𝟙 X') z _ a = ((Geo.Tor.gw w (𝟙 _) z k k')⁻¹).val * gs φ z _ (s.f k) := by
    intro k'
    let W : H.ι → X'.Opens := fun k => (H.pull φ).U (fun _ => k) ⊓ H'.U k'
    have l₁ : ∀ k, W k ≤ φ ⁻¹ᵁ H.U k := fun k x hx => mem_pull.1 hx.1
    obtain ⟨u, hu⟩ : ∃ u : ∀ k, Γ(X', W k), ∀ (z : X') k, z ∈ W k →
        gs (𝟙 X') z (W k) (u k) = ((Geo.Tor.gw w (𝟙 _) z k k')⁻¹).val * gs φ z _ (s.f k) :=
      ⟨fun k => ((show Γ(X', W k)ˣ from w.s (fun _ => k, k'))⁻¹).val *
          (X'.presheaf.map (homOfLE (l₁ k)).op).hom ((φ.app _).hom (s.f k)), fun z k hz =>
        (gs_mul (𝟙 X') z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit (𝟙 X') z _ hz _).trans (congrArg Units.val (map_inv _ _)))
          ((gs_res (𝟙 X') z _ hz _).trans ((gs_pull (𝟙 X') φ z _ (l₁ k hz) _).trans (by rw [Category.id_comp]))))⟩
    obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' W (H'.U k')
      (fun k => homOfLE inf_le_right) (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hH (φ y)
        exact Opens.mem_iSup.2 ⟨k, mem_pull.2 hk, hy⟩) u
      (fun k j => fn_ext (V := W k ⊓ W j) fun y hy => by
        refine (gs_res (𝟙 X') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X') y inf_le_right hy _).symm)
        rw [hu y k hy.1, hu y j hy.2, ind y k j k' k' (l₁ k hy.1) (l₁ j hy.2) hy.1.2 hy.1.2,
          gm_self hH' (𝟙 X') y hy.1.2, Units.val_one, _root_.one_mul])
    refine ⟨a, fun z k h₁ h₂ => ?_⟩
    have hz : z ∈ W k := ⟨mem_pull.2 h₁, h₂⟩
    exact (gs_res (𝟙 X') z inf_le_right hz a).symm.trans ((congrArg (gs (𝟙 X') z (W k)) (ha k)).trans
      (hu z k hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun z k k' hk hk' => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hH (φ y)
    refine (gs_res (𝟙 X') y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 X') y _ hy _ _).trans (congrArg₂ (· * ·)
      (gs_unit (𝟙 X') y _ hy _) (gs_res (𝟙 X') y _ hy _))).symm)
    rw [ha j y k hk hy.1, ha j' y k hk hy.2]
    exact ind y k k j j' hk hk hy.1 hy.2
  · show _ = _ * gs (𝟙 X') z _ (a k')
    rw [ha k' z k hk hk', Units.mul_inv_cancel_left]
end GlobalTheory.SecPullIso
