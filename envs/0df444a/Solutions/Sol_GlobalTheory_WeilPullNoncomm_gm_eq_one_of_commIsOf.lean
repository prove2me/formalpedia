-- Prove2me | solution 1 for GlobalTheory.WeilPullNoncomm.gm_eq_one_of_commIsOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:31:47.342344+00:00
-- url     : https://prove2.me/submissions/fb385835-4855-45e4-8680-69fb8b8c7cb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotWeilIsGrpPullback
import Theorems.Thm_GlobalTheory_WeilPullNoncomm_manyChart_isLB
import Theorems.Thm_GlobalTheory_WeilPullNoncomm_tval_manyChart
import Theorems.Thm_GlobalTheory_CommPairing_commIsOf_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open GlobalTheory GlobalTheory.WeilPullNoncomm
open GlobalTheory.CommPairing
variable {S : Scheme.{0}} {G : Over S} [GrpObj G]
namespace GlobalTheory.WeilPullNoncomm
theorem _root_.solution (u : Γ(G.left, ⊤)ˣ) {T : Over S}
    {θx θy : ThetaGrp G (manyChart (fun b : Bool => if b then u else 1)) 1 T} {c : Γ(T.left, ⊤)ˣ}
    (H : CommIsOf G _ 1 θx θy c) (hn : θx.pt * θy.pt ≠ θy.pt * θx.pt) (z : T.left) :
    ∃ r : T.left ⟶ G.left, gm r z ⊤ u = 1 := by
  classical
  rw [commIsOf_iff (manyChart_isLB _)] at H
  let r : T ⟶ T ⊗ G := lift (𝟙 T) 1
  have s : ∀ x : T ⟶ G, (r.left ≫ (translT G x).left) ≫ (snd T G).left = r.left ≫ (translPt G x).left := fun x => by
    rw [Category.assoc, ← Over.comp_left, translT, lift_snd]
  have q : ∀ x y : T ⟶ G, (r.left ≫ (translT G x).left) ≫ (translPt G y).left = (y * x).left := fun x y => by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    show (r ≫ lift (fst T G) ((fst T G ≫ x) * snd T G)) ≫ ((fst T G ≫ y) * snd T G) = _
    simp [r, MonObj.comp_mul, comp_lift]
  have hPQ : (θy.pt * θx.pt).left ≠ (θx.pt * θy.pt).left := fun h => hn (Over.OverMorphism.ext h.symm)
  let J : (T.left ⟶ G.left) → Bool := fun ψ => decide (ψ = (θx.pt * θy.pt).left)
  have h₁ := H _ r.left z J (fun _ => trivial)
  have h₂ := H _ r.left z (fun _ => false) (fun _ => trivial)
  rw [tval_manyChart _ θx r.left z J (fun _ => false), tval_manyChart _ θy r.left z J (fun _ => false),
    tval_manyChart _ θx _ z J (fun _ => false), tval_manyChart _ θy _ z J (fun _ => false), s, s, q, q] at h₁
  have j₁ : J (θx.pt * θy.pt).left = true := decide_eq_true rfl
  have j₂ : J (θy.pt * θx.pt).left = false := decide_eq_false hPQ
  rw [j₁, j₂] at h₁
  simp only [Bool.false_eq_true, if_false, if_true, map_one, inv_one, _root_.mul_one, zpow_neg, zpow_one] at h₁
  refine ⟨(θx.pt * θy.pt).left, ?_⟩
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul h₁
  have a₂ := congrArg Additive.ofMul h₂
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ ⊢
  linear_combination (norm := abel) a₁ - a₂
end GlobalTheory.WeilPullNoncomm
