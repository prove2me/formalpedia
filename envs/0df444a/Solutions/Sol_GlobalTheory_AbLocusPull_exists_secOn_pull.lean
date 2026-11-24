-- Prove2me | solution 1 for GlobalTheory.AbLocusPull.exists_secOn_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:53:06.581537+00:00
-- url     : https://prove2.me/submissions/ddb39dda-3eef-4f08-8e2a-67e9ecbe5962

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProperRestrictPull
import Theorems.Thm_GlobalTheory_AbLocusPull_isUnit_gs_iff
import Theorems.Thm_GlobalTheory_AbLocusPull_glue_fn
import Theorems.Thm_GlobalTheory_AbLocusPull_gs_secOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
namespace GlobalTheory.AbLocusPull
variable {X Y Z : Scheme.{0}}
private lemma toFld_gm_res {T : Scheme.{0}} {U V : T.Opens} (h : V ≤ U) (y : T) (hy : y ∈ V) (u : Γ(T, U)ˣ) :
    gm (𝟙 T) y V (res h u) = gm (𝟙 T) y U u :=
  Units.ext ((gs_unit (𝟙 T) y V hy (res h u)).symm.trans
    ((gs_res (𝟙 T) y h hy u.val).trans (gs_unit (𝟙 T) y U (h hy) u)))
private lemma gm_id_pull_g_eq_gm_comp {A B : Scheme.{0}} (L : LB A) (F : B ⟶ A) (x : B) (J J' : (L.pull F).ι)
    (h1 : x ∈ (L.pull F).U J) (h2 : x ∈ (L.pull F).U J') :
    gm (𝟙 B) x ((L.pull F).U J ⊓ (L.pull F).U J') ((L.pull F).g J J') =
      gm F x (L.U (J ⟨⟩) ⊓ L.U (J' ⟨⟩)) (L.g (J ⟨⟩) (J' ⟨⟩)) := by
  have e := gm_linComb L (fun _ : PUnit => F) (fun _ => 1) (𝟙 B) x J J' h1 h2
  simp only [Finset.univ_unique, Finset.prod_singleton, zpow_one, Category.id_comp] at e
  exact e
private lemma gm_id_div_g_eq_mul_inv {T : Scheme.{0}} (M N : LB T) (y : T) (p q : M.ι × N.ι)
    (hy : y ∈ (M.div N).U p ⊓ (M.div N).U q) :
    gm (𝟙 T) y ((M.div N).U p ⊓ (M.div N).U q) ((M.div N).g p q) =
      gm (𝟙 T) y (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) * (gm (𝟙 T) y (N.U p.2 ⊓ N.U q.2) (N.g p.2 q.2))⁻¹ := by
  show gm (𝟙 T) y _ (res _ (M.g p.1 q.1) * (res _ (N.g p.2 q.2))⁻¹) = _
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (toFld_gm_res _ y hy _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (toFld_gm_res _ y hy _))))
end GlobalTheory.AbLocusPull
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.AbLocusPull
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.AbLocusPull
theorem _root_.solution {X' : Scheme.{0}} {F : X' ⟶ X} {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull F)) {W : X.Opens} {W' : X'.Opens} (hW : W' ≤ F ⁻¹ᵁ W) {θ : ∀ i, Γ(X, W ⊓ L.U i)}
    (hθ : θ ∈ secOn L W) :
    ∃ θ' ∈ secOn L' W', ∀ x ∈ W', ∀ j k, x ∈ L'.U k → F x ∈ X.basicOpen (θ j) → x ∈ X'.basicOpen (θ' k) := by
  obtain ⟨w, hwg⟩ := hw
  obtain ⟨hcovL, -, -⟩ := hL
  obtain ⟨-, hself', -⟩ := hL'
  have m1 : ∀ (J : (L.pull F).ι) (y : X'), y ∈ (L.pull F).U J ↔ F y ∈ L.U (J ⟨⟩) := fun J y => by
    simp [LB.pull, LB.LinComb, LB.wchart]
    exact ⟨fun h => h _, fun h _ => h⟩
  have hchart : ∀ y : X, ∃ i, y ∈ L.U i := fun y => by
    have hy : y ∈ (⨆ i, L.U i) := by rw [hcovL]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hy
  have hwrel : ∀ (x : X') (J J' : (L.pull F).ι) (k k' : L'.ι), x ∈ (L.pull F).U J ⊓ L'.U k →
      x ∈ (L.pull F).U J' ⊓ L'.U k' →
      gm (𝟙 X') x ((L.pull F).U J ⊓ L'.U k) (w.s (J, k)) =
        gm F x (L.U (J ⟨⟩) ⊓ L.U (J' ⟨⟩)) (L.g (J ⟨⟩) (J' ⟨⟩)) *
          (gm (𝟙 X') x (L'.U k ⊓ L'.U k') (L'.g k k'))⁻¹ * gm (𝟙 X') x ((L.pull F).U J' ⊓ L'.U k') (w.s (J', k')) := by
    intro x J J' k k' h1 h2
    have h12 : x ∈ ((L.pull F).div L').U (J, k) ⊓ ((L.pull F).div L').U (J', k') := ⟨h1, h2⟩
    have e := congrArg (gm (𝟙 X') x (((L.pull F).div L').U (J, k) ⊓ ((L.pull F).div L').U (J', k')))
      (hwg (J, k) (J', k'))
    rw [map_mul, toFld_gm_res _ x h12, toFld_gm_res _ x h12, gm_id_div_g_eq_mul_inv (L.pull F) L' x (J, k) (J', k') h12,
      gm_id_pull_g_eq_gm_comp L F x J J' h1.1 h2.1] at e
    exact e
  have hone : ∀ k x, x ∈ L'.U k → gm (𝟙 X') x (L'.U k ⊓ L'.U k) (L'.g k k) = 1 := by
    intro k x hx
    have e := congrArg (gm (𝟙 X') x (L'.U k)) (hself' k)
    rwa [map_one, toFld_gm_res _ x hx] at e
  have hind : ∀ (x : X') (J J' : (L.pull F).ι) (k k' : L'.ι), x ∈ (L.pull F).U J ⊓ L'.U k →
      x ∈ (L.pull F).U J' ⊓ L'.U k' → F x ∈ W →
      gs F x (W ⊓ L.U (J ⟨⟩)) (θ (J ⟨⟩)) * ((gm (𝟙 X') x ((L.pull F).U J ⊓ L'.U k) (w.s (J, k)))⁻¹).val =
        (gm (𝟙 X') x (L'.U k ⊓ L'.U k') (L'.g k k')).val *
          (gs F x (W ⊓ L.U (J' ⟨⟩)) (θ (J' ⟨⟩)) *
            ((gm (𝟙 X') x ((L.pull F).U J' ⊓ L'.U k') (w.s (J', k')))⁻¹).val) := by
    intro x J J' k k' h1 h2 hxW
    rw [gs_secOn hθ F x (J ⟨⟩) (J' ⟨⟩) hxW ((m1 J x).1 h1.1) ((m1 J' x).1 h2.1), hwrel x J J' k k' h1 h2]
    simp only [mul_inv_rev, inv_inv, Units.val_mul]
    linear_combination (gs F x (W ⊓ L.U (J' ⟨⟩)) (θ (J' ⟨⟩)) *
      ((gm (𝟙 X') x ((L.pull F).U J' ⊓ L'.U k') (w.s (J', k')))⁻¹).val *
      (gm (𝟙 X') x (L'.U k ⊓ L'.U k') (L'.g k k')).val) *
      Units.mul_inv (gm F x (L.U (J ⟨⟩) ⊓ L.U (J' ⟨⟩)) (L.g (J ⟨⟩) (J' ⟨⟩)))
  have hOa : ∀ k J, W' ⊓ L'.U k ⊓ (L.pull F).U J ≤ F ⁻¹ᵁ (W ⊓ L.U (J ⟨⟩)) := fun k J x hx =>
    (show F x ∈ W ⊓ L.U (J ⟨⟩) from ⟨hW hx.1.1, (m1 J x).1 hx.2⟩)
  have hOb : ∀ k J, W' ⊓ L'.U k ⊓ (L.pull F).U J ≤ (L.pull F).U J ⊓ L'.U k := fun k J x hx =>
    (show x ∈ (L.pull F).U J ⊓ L'.U k from ⟨hx.2, hx.1.2⟩)
  obtain ⟨a, ha⟩ : ∃ a : ∀ k J, Γ(X', W' ⊓ L'.U k ⊓ (L.pull F).U J), ∀ k J, a k J =
      (X'.presheaf.map (homOfLE (hOa k J)).op).hom ((F.app (W ⊓ L.U (J ⟨⟩))).hom (θ (J ⟨⟩))) *
        ((res (hOb k J) (w.s (J, k)))⁻¹).val := ⟨_, fun _ _ => rfl⟩
  have hE : ∀ k J x (hx : x ∈ W' ⊓ L'.U k ⊓ (L.pull F).U J),
      gs (𝟙 X') x _ (a k J) = gs F x (W ⊓ L.U (J ⟨⟩)) (θ (J ⟨⟩)) *
        ((gm (𝟙 X') x ((L.pull F).U J ⊓ L'.U k) (w.s (J, k)))⁻¹).val := by
    intro k J x hx
    rw [ha, gs_mul (𝟙 X') x _ hx, gs_res (𝟙 X') x _ hx, gs_pull (𝟙 X') F x _ (hOa k J hx), Category.id_comp,
      gs_unit (𝟙 X') x _ hx, map_inv, toFld_gm_res (hOb k J) x hx (w.s (J, k))]
  have hglue : ∀ k, ∃ b : Γ(X', W' ⊓ L'.U k), ∀ x J, x ∈ W' ⊓ L'.U k ⊓ (L.pull F).U J →
      gs (𝟙 X') x (W' ⊓ L'.U k) b = gs (𝟙 X') x _ (a k J) := by
    intro k
    obtain ⟨b, hb⟩ := glue_fn (W' ⊓ L'.U k) (fun J => W' ⊓ L'.U k ⊓ (L.pull F).U J) (fun J => inf_le_left)
      (fun x hx => by
        obtain ⟨i, hi⟩ := hchart (F x)
        exact ⟨fun _ => i, (show x ∈ W' ⊓ L'.U k ⊓ (L.pull F).U (fun _ => i) from ⟨hx, (m1 _ x).2 hi⟩)⟩)
      (a k) (fun J J' x hx hx' => by
        rw [hE k J x hx, hE k J' x hx', hind x J J' k k ⟨hx.2, hx.1.2⟩ ⟨hx'.2, hx'.1.2⟩ (hW hx.1.1),
          hone k x hx.1.2, Units.val_one, _root_.one_mul])
    exact ⟨b, fun x J hx => hb x J hx⟩
  choose θ' hθ' using hglue
  refine ⟨θ', ?_, ?_⟩
  · intro k k'
    apply fn_ext
    intro x hx
    dsimp only [resG]
    rw [gs_mul (𝟙 X') x _ hx, gs_res (𝟙 X') x _ hx, gs_res (𝟙 X') x _ hx, gs_res (𝟙 X') x _ hx,
      gs_unit (𝟙 X') x _ (show x ∈ L'.U k ⊓ L'.U k' from ⟨hx.1.2, hx.2⟩)]
    obtain ⟨i, hi⟩ := hchart (F x)
    have hx1 : x ∈ W' ⊓ L'.U k ⊓ (L.pull F).U (fun _ => i) := ⟨hx.1, (m1 _ x).2 hi⟩
    have hx2 : x ∈ W' ⊓ L'.U k' ⊓ (L.pull F).U (fun _ => i) := ⟨⟨hx.1.1, hx.2⟩, (m1 _ x).2 hi⟩
    rw [hθ' k x _ hx1, hθ' k' x _ hx2, hE k _ x hx1, hE k' _ x hx2]
    exact hind x _ _ k k' ⟨hx1.2, hx1.1.2⟩ ⟨hx2.2, hx2.1.2⟩ (hW hx.1.1)
  · intro x hxW j k hk hj
    have hFj : F x ∈ W ⊓ L.U j := Scheme.basicOpen_le X (θ j) hj
    have hx1 : x ∈ W' ⊓ L'.U k ⊓ (L.pull F).U (fun _ => j) := ⟨⟨hxW, hk⟩, (m1 _ x).2 hFj.2⟩
    have hu : IsUnit (gs (𝟙 X') x (W' ⊓ L'.U k) (θ' k)) := by
      rw [hθ' k x _ hx1, hE k _ x hx1]
      exact ((isUnit_gs_iff F x _ hFj (θ j)).2 hj).mul (Units.isUnit _)
    exact (isUnit_gs_iff (𝟙 X') x (W' ⊓ L'.U k) ⟨hxW, hk⟩ (θ' k)).1 hu
end GlobalTheory.AbLocusPull
