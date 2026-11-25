-- Prove2me | solution 1 for GlobalTheory.ThetaPtMove.isTwistPull_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:23:12.621829+00:00
-- url     : https://prove2.me/submissions/94756607-a215-4295-a5c6-b21c54667ccb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Theorems.Thm_GlobalTheory_ThetaPtMove_psi_lift
import Theorems.Thm_GlobalTheory_VVRank_isTwistPull_of_sv
import Theorems.Thm_GlobalTheory_VVRank_sv_of_isTwistPull
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
theorem _root_.solution (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a b : ℤ} {m : T ⊗ A ⟶ A}
    {m₀ : T₀ ⊗ G ⟶ G} (h : psi hp τ hτ ≫ m₀.left = m.left ≫ φ)
    {α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, m₀.left] ![a, -b])}
    {α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : α.IsGen)
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
        val α₀ (r ≫ psi hp τ hτ) z J =
          (wVal w z J J' (r ≫ (snd T A).left) ^ a * wVal w z J J' (r ≫ m.left) ^ (-b)) * val α r z J')
    {s₀ s₀' s s'} (hs : SecRel hp τ hτ w s s₀) (hs' : SecRel hp τ hτ w s' s₀')
    (H₀ : IsTwistPull G L₀ (lift (fst T₀ G) m₀) m₀ (lift_snd _ _) a b α₀ s₀ s₀') :
    IsTwistPull A L₁ (lift (fst T A) m) m (lift_snd _ _) a b α s s' := by
  refine VVRank.isTwistPull_of_sv A hL₁ hα fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' hL₀ y
  have q := VVRank.sv_of_isTwistPull G H₀ (𝟙 _ ≫ psi hp τ hτ) y hJ
  have e : (𝟙 _ ≫ (lift (fst T A) m).left) ≫ (snd T A).left = 𝟙 _ ≫ m.left := by
    rw [Category.assoc, ← Over.comp_left, lift_snd]
  rw [hs' _ _ _ _ _ hJ hJ', H _ _ _ _ _ hJ hJ', Category.assoc, ← psi_lift hp τ hτ h, ← Category.assoc,
    hs _ _ _ _ _ hJ hJ', e, zpow_neg] at q
  refine (Units.mul_right_inj _).1 (q.trans ?_)
  simp only [Units.val_mul]
  rw [mul_right_comm _ _ (val α _ y J').val, _root_.mul_assoc, Units.inv_mul_cancel_left, _root_.mul_assoc]
end GlobalTheory.ThetaPtMove
