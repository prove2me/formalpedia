-- Prove2me | solution 1 for GlobalTheory.SecPull.exists_down_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:50:26.496796+00:00
-- url     : https://prove2.me/submissions/36a89648-b31d-487c-8685-a8a62ccf7b09

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Theorems.Thm_GlobalTheory_SecPull_mem_wchart_comp
import Theorems.Thm_GlobalTheory_SecPull_trF_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_pw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pw_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_trF_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecPull
variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace GlobalTheory.SecPull
theorem _root_.solution {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ)
    (s : LB.Sec (LB.LinComb L φ ε)) : ∃ a : LB.Sec (LB.LinComb L' φ' ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
        gs r z (LB.wchart L' φ' q) (a.f q) =
          (pw w φ' ε r z p q)⁻¹.val * gs (r ≫ h) z (LB.wchart L φ p) (s.f p) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ a : Γ(Y', LB.wchart L' φ' q), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gs r z _ a = (pw w φ' ε r z p q)⁻¹.val * gs (r ≫ h) z (LB.wchart L φ p) (s.f p) := by
    intro q
    let W : (K → L.ι) → Y'.Opens := fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q
    have le : ∀ p, W p ≤ h ⁻¹ᵁ LB.wchart L φ p := fun p y hy => mem_wchart_comp hc hy.1
    obtain ⟨v, hv⟩ : ∃ v : ∀ p, Γ(Y', W p), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p, r z ∈ W p →
        gs r z (W p) (v p) = (pw w φ' ε r z p q)⁻¹.val * gs (r ≫ h) z (LB.wchart L φ p) (s.f p) :=
      ⟨fun p => (u p q)⁻¹.val * (Y'.presheaf.map (homOfLE (le p)).op).hom ((h.app _).hom (s.f p)),
        fun Z r z p hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit r z _ hz _).trans (congrArg Units.val ((map_inv _ _).trans (congrArg (·⁻¹) (hu p q Z r z hz)))))
          ((gs_res r z (le p) hz _).trans (gs_pull r h z _ (le p hz) _)))⟩
    obtain ⟨a, ha, -⟩ := Y'.sheaf.existsUnique_gluing' W (LB.wchart L' φ' q)
      (fun p => homOfLE inf_le_right) (fun y hy => by
        choose p hp using fun k => exists_chart hL (F (φ' k y))
        exact Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) v
      (fun p p' => fn_ext (V := W p ⊓ W p') fun y hy => by
        refine (gs_res (𝟙 Y') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y') y inf_le_right hy _).symm)
        rw [hv _ _ y p hy.1, hv _ _ y p' hy.2, sec_trans s (𝟙 Y' ≫ h) y (le p hy.1) (le p' hy.2), trF_comp hc,
          pw_trans hw φ' ε (𝟙 Y') y hy.1.1 hy.2.1 hy.1.2 hy.1.2, trF_self hL' _ ε (𝟙 Y') y hy.1.2, inv_one, mul_one,
          ← mul_assoc, ← Units.val_mul, mul_inv_rev, inv_mul_cancel_right])
    refine ⟨a, fun Z r z p h₁ h₂ => ?_⟩
    have hz : r z ∈ W p := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_right hz a).symm.trans ((congrArg (gs r z (W p)) (ha p)).trans (hv Z r z p hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z p q => ha q Z r z p⟩
  choose p hp using fun k => exists_chart hL (F (φ' k y))
  have m : (𝟙 Y' : Y' ⟶ Y') y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
  refine (gs_res (𝟙 Y') y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans (congrArg₂ (· * ·)
    ((gs_unit (𝟙 Y') y _ hy _).trans (congrArg Units.val (gm_linComb L' φ' ε (𝟙 Y') y j j' hy.1 hy.2)))
    (gs_res (𝟙 Y') y _ hy _))).symm)
  refine (ha j _ (𝟙 Y') y p m hy.1).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 Y') y p m hy.2)).symm)
  rw [pw_trans hw φ' ε (𝟙 Y') y m m hy.1 hy.2, trF_self hL _ ε (𝟙 Y') y m, one_mul, mul_inv, inv_inv, Units.val_mul,
    mul_assoc]
  rfl
end GlobalTheory.SecPull
