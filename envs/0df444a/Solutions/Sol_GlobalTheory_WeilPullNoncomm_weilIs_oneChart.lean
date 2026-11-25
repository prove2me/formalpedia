-- Prove2me | solution 1 for GlobalTheory.WeilPullNoncomm.weilIs_oneChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:48:13.435146+00:00
-- url     : https://prove2.me/submissions/0364818e-1056-48f7-9bb4-2c534a77a250

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotWeilIsGrpPullback
import Theorems.Thm_GlobalTheory_WeilPullNoncomm_oneChart_isLB
import Theorems.Thm_GlobalTheory_WeilPullNoncomm_one_isGen
import Theorems.Thm_GlobalTheory_CommPairing_commIsOf_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
theorem _root_.solution (hu : ∀ u : Γ(G.left, ⊤)ˣ, ∃ a : Γ(S, ⊤)ˣ, u = pullU G.hom ⊤ a) {T : Over S} [IsIso T.hom]
    (k : ℤ) (x y : T ⟶ G) : WeilIs G (oneChart _) k x y 1 := by
  intro p
  refine ⟨⊤, trivial, ⟨⟨_, _, one_isGen _ _⟩, ⟨_, _, one_isGen _ _⟩, rfl, rfl⟩, fun θx θy h₁ h₂ => ?_⟩
  have hi : IsIso (overRes (⊤ : T.left.Opens)).hom := by
    show IsIso ((⊤ : T.left.Opens).ι ≫ T.hom)
    have : IsIso (⊤ : T.left.Opens).ι := inferInstanceAs (IsIso T.left.topIso.hom)
    infer_instance
  have e1 : unitRes (⊤ : T.left.Opens) 1 = 1 := map_one _
  rw [e1]
  clear e1 h₁ h₂
  generalize overRes (⊤ : T.left.Opens) = T' at *
  have hs : IsIso (snd T' G).left := inferInstanceAs (IsIso (pullback.snd T'.hom G.hom))
  have key : ∀ θ : ThetaGrp G (oneChart _) k T', ∃ a : Γ(S, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ G).left) (z : Z) (J),
      tval θ r z J = gm (r ≫ (T' ⊗ G).hom) z ⊤ a := by
    intro θ
    have le : ⊤ ≤ LB.wchart (oneChart G.left) ![(snd T' G).left, (translPt G θ.pt).left] (fun _ => PUnit.unit) :=
      fun _ _ => Set.mem_iInter.2 fun _ => trivial
    obtain ⟨a, ha⟩ := hu (pullU (inv (snd T' G).left) ⊤ (res le (θ.φ.s fun _ => PUnit.unit)))
    refine ⟨a, fun Z r z J => ?_⟩
    have h := congrArg (gm (r ≫ (snd T' G).left) z ⊤) ha
    have h₁ := gm_pull (r ≫ (snd T' G).left) (inv (snd T' G).left) z ⊤ trivial (res le (θ.φ.s fun _ => PUnit.unit))
    have h₂ := gm_pull (r ≫ (snd T' G).left) G.hom z ⊤ trivial a
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h₁
    rw [Category.assoc, Over.w] at h₂
    exact (gm_res r z le trivial _).symm.trans (h₁.symm.trans (h.trans h₂))
  obtain ⟨a, ha⟩ := key θx
  obtain ⟨b, hb⟩ := key θy
  rw [commIsOf_iff (oneChart_isLB _)]
  intro Z r z J _
  rw [ha, ha, hb, hb, Category.assoc, Category.assoc, Over.w, Over.w, map_one, _root_.mul_one, mul_comm]
end GlobalTheory.WeilPullNoncomm
