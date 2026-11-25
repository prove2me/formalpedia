-- Prove2me | solution 1 for GlobalTheory.ThetaPtMove.exists_secRel_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:01:30.384865+00:00
-- url     : https://prove2.me/submissions/0ce96978-17a8-4e9f-af17-98d8edb3f178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Theorems.Thm_P2M_GlobalTheory_ThetaPtMove_psi_snd__014c8d7c58c3
import Theorems.Thm_GlobalTheory_ConstFam_exists_sec_up
import Theorems.Thm_GlobalTheory_VVRank_sval_pullTo
import Theorems.Thm_GlobalTheory_WeilPull_exists_psi_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff


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
open GlobalTheory GlobalTheory.ThetaPtMove
open GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
variable {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}
namespace GlobalTheory.ThetaPtMove
theorem _root_.solution [IsIso τ] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ}
    (s : LB.Sec (LPow A L₁ a T)) : ∃ s₀, SecRel hp τ hτ w s s₀ := by
  obtain ⟨χ, h₁, h₂⟩ := WeilPull.exists_psi_inv hp τ hτ
  obtain ⟨t, ht⟩ := exists_sec_up ((isGen_iff w).1 hw) hL₀ hL₁ (φ' := fun _ : Fin 1 => (snd T A).left)
    (ε := fun _ => a) s
  have h₁' : psi hp τ hτ ≫ χ = 𝟙 _ := h₁
  have h₂' : χ ≫ psi hp τ hτ = 𝟙 _ := h₂
  have e₀ : χ ≫ (snd T A).left ≫ φ = (snd T₀ G).left := by
    rw [← psi_snd' hp τ hτ, ← Category.assoc, h₂', Category.id_comp]
  refine ⟨VVRank.pullTo (φ' := fun _ : Fin 1 => (snd T₀ G).left) t χ fun _ => e₀, fun Z r z J J' hJ hJ' => ?_⟩
  refine (VVRank.sval_pullTo _ _ _ _ z hJ).trans ?_
  rw [Category.assoc, h₁', Category.comp_id]
  refine (ht Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (congrArg Units.val ?_) rfl)
  simp only [pw, wVal, Fin.prod_univ_one, Category.assoc]
end GlobalTheory.ThetaPtMove
