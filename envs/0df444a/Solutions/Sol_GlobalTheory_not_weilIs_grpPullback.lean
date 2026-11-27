-- Prove2me | solution 1 for GlobalTheory.not_weilIs_grpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:42:27.289252+00:00
-- url     : https://prove2.me/submissions/c8bd562f-e24c-4345-9990-f8ce3ec2d3d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotWeilIsGrpPullback
import Theorems.Thm_GlobalTheory_WeilPullNoncomm_oneChart_isLB
import Theorems.Thm_GlobalTheory_WeilPullNoncomm_manyChart_isLB
import Theorems.Thm_GlobalTheory_WeilPullNoncomm_manyChart_iso
import Theorems.Thm_GlobalTheory_WeilPullNoncomm_weilIs_oneChart
import Theorems.Thm_GlobalTheory_WeilPullNoncomm_gm_eq_one_of_commIsOf
import Theorems.Thm_GlobalTheory_WeilPullNoncomm_heisEquiv_mul
import Theorems.Thm_GlobalTheory_WeilPullNoncomm_heisEquiv_comp
import Theorems.Thm_GlobalTheory_WeilPullNoncomm_heis_units
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_of_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open WeilPullNoncomm
namespace GlobalTheory
theorem _root_.solution : ¬ ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G']
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB →
    IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → ∀ (T : Over S') (k : ℤ) (x y : T ⟶ G')
    (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ φ → y₀.left = y.left ≫ φ →
    (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c) := by
  intro H
  let S : Scheme.{0} := Spec (.of ℚ)
  have h2 : IsUnit (2 : Γ(S, ⊤)) := by
    have := (IsUnit.mk0 (2 : ℚ) two_ne_zero).map (Scheme.ΓSpecIso (.of ℚ)).inv.hom
    rwa [map_ofNat] at this
  let G := heisObj S
  let u : Γ(G.left, ⊤)ˣ := pullU G.hom ⊤ h2.unit
  let T : Over S := Over.mk (𝟙 S)
  let x : T ⟶ G := (heisEquiv T).symm ⟨1, 0, 0⟩
  let y : T ⟶ G := (heisEquiv T).symm ⟨0, 1, 0⟩
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  have hp := isGrpPullback_of_iso (Iso.refl G)
  have : IsIso (Over.mk (T.hom ≫ 𝟙 S)).hom := inferInstanceAs (IsIso (𝟙 S ≫ 𝟙 S))
  have W := (H S S G G _ _ (oneChart _) (manyChart fun b : Bool => if b then u else 1) (oneChart_isLB _)
    (manyChart_isLB _) hp (manyChart_iso _ _) T 1 x y (pushPt hp.1.w x) (pushPt hp.1.w y) 1 rfl rfl).2
    (weilIs_oneChart (heis_units S) _ _ _)
  obtain ⟨p⟩ : Nonempty S := inferInstance
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, hc⟩ := W p
  have : Nonempty V := ⟨⟨p, hV⟩⟩
  have : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨⟨p, hV⟩, trivial⟩⟩
  obtain ⟨r, hr⟩ := gm_eq_one_of_commIsOf u (hc θx θy hx hy) (fun h => by
    have e₀ := (heisEquiv_mul θx.pt θy.pt).symm.trans ((congrArg (heisEquiv _) h).trans (heisEquiv_mul θy.pt θx.pt))
    have ex : heisEquiv _ θx.pt = Heis.map V.ι.appTop.hom ⟨1, 0, 0⟩ := (congrArg (heisEquiv _) hx).trans
      ((heisEquiv_comp _ _).trans (congrArg _ ((heisEquiv T).apply_symm_apply _)))
    have ey : heisEquiv _ θy.pt = Heis.map V.ι.appTop.hom ⟨0, 1, 0⟩ := (congrArg (heisEquiv _) hy).trans
      ((heisEquiv_comp _ _).trans (congrArg _ ((heisEquiv T).apply_symm_apply _)))
    rw [ex, ey] at e₀
    have e := congrArg Heis.c e₀
    have e' : V.ι.appTop.hom 0 + V.ι.appTop.hom 0 + V.ι.appTop.hom 1 * V.ι.appTop.hom 1 =
      V.ι.appTop.hom 0 + V.ι.appTop.hom 0 + V.ι.appTop.hom 0 * V.ι.appTop.hom 0 := e
    simp at e') ⟨p, hV⟩
  have e := congrArg Units.val ((gm_pull r G.hom _ ⊤ trivial h2.unit).symm.trans hr)
  replace e := (gm_val (r ≫ G.hom) _ ⊤ trivial h2.unit).symm.trans e
  rw [IsUnit.unit_spec, map_ofNat, map_ofNat, Units.val_one] at e
  have nt : Nontrivial ((overRes V).left.presheaf.stalk (⟨p, hV⟩ : V.toScheme)) :=
    (V.toScheme.toLocallyRingedSpace.isLocalRing ⟨p, hV⟩).toNontrivial
  exact one_ne_zero (α := (overRes V).left.presheaf.stalk (⟨p, hV⟩ : V.toScheme)) (add_left_cancel (a := 1) ((one_add_one_eq_two.trans e).trans (add_zero _).symm))
end GlobalTheory
