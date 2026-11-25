-- Prove2me | solution 1 for GlobalTheory.ThetaPtMove.isGenSec_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:43:04.501664+00:00
-- url     : https://prove2.me/submissions/7bcaf79c-641e-43a8-9365-16fb1247dad4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Theorems.Thm_P2M_GlobalTheory_ThetaPtMove_psi_fst__593f73f6caa4
import Theorems.Thm_P2M_GlobalTheory_ThetaPtMove_psi_snd__014c8d7c58c3
import Theorems.Thm_GlobalTheory_ThetaPtMove_psi_ext
import Theorems.Thm_GlobalTheory_ThetaPtMove_exists_secRel_up
import Theorems.Thm_GlobalTheory_ThetaPtMove_sv_of_eq_mul
import Theorems.Thm_GlobalTheory_ThetaAct_sv_ext
import Theorems.Thm_GlobalTheory_ThetaAct_sv_smul
import Theorems.Thm_GlobalTheory_VVRank_sv_pullS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
theorem _root_.solution (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} {B : Over S} (σ : T.left ⟶ B.left)
    [IsIso σ] (β : B ⟶ T₀) (hβ : σ ≫ β.left = τ) {th : LB.Sec (LPow A L₁ a T)} {th₀ : LB.Sec (LPow G L₀ a T₀)}
    (h : SecRel hp τ hτ w th th₀) (hg : IsGenSec G L₀ a (VVRank.pullS G a β th₀)) : IsGenSec A L₁ a th := by
  intro s
  have hσ : σ ≫ B.hom = T.hom ≫ f := by rw [← Over.w β, ← Category.assoc, hβ, hτ]
  obtain ⟨s₀, hs⟩ := exists_secRel_up hp σ hσ hw hL₀ hL₁ s
  obtain ⟨c, hc⟩ := hg s₀
  have e : psi hp σ hσ ≫ (β ▷ G).left = psi hp τ hτ := by
    refine psi_ext ?_ ?_
    · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst', psi_fst',
        Category.assoc, hβ]
    · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', psi_snd']
  have key : SecM.ofSec A s = σ.appTop.hom c • SecM.ofSec A th := ThetaAct.sv_ext hL₁ fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    have q := sv_of_eq_mul hc (𝟙 _ ≫ psi hp σ hσ) y hJ
    rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, Category.assoc (𝟙 _) _ (β ▷ G).left, e, hs _ _ _ _ _ hJ hJ',
      h _ _ _ _ _ hJ hJ', mul_left_comm, Category.assoc (𝟙 _) _ (fst B G).left, psi_fst', ← Category.assoc] at q
    refine Eq.trans ?_ (ThetaAct.sv_smul _ _ _ _ hJ').symm
    exact ((Units.mul_right_inj _).1 q).trans (congrArg (· * _) (gs_pull _ σ y ⊤ trivial c).symm)
  exact ⟨σ.appTop.hom c, fun j => congrArg (fun q => q.1 j) key⟩
end GlobalTheory.ThetaPtMove
