-- Prove2me | solution 1 for GlobalTheory.ThetaPtUp.isTwistPull_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:23:49.380718+00:00
-- url     : https://prove2.me/submissions/4e2c72e0-c391-4a3a-ae09-83a7b450d7e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HasThetaConstantsIffOfThetaLevelPullback
import Theorems.Thm_P2M_GlobalTheory_ThetaPtUp_exists_psi_inv__3417de49043e
import Theorems.Thm_GlobalTheory_ThetaPtMove_psi_lift
import Theorems.Thm_GlobalTheory_VVRank_isTwistPull_of_sv
import Theorems.Thm_GlobalTheory_VVRank_sv_of_isTwistPull


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ThetaPtUp
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift GlobalTheory.ThetaPtMove
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) [IsIso τ] (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}
namespace GlobalTheory.ThetaPtUp
theorem _root_.solution (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a b : ℤ} {m : T ⊗ A ⟶ A}
    {m₀ : T₀ ⊗ G ⟶ G} (h : psi hp τ hτ ≫ m₀.left = m.left ≫ φ)
    {α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, m₀.left] ![a, -b])}
    {α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα₀ : α₀.IsGen)
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
        val α₀ (r ≫ psi hp τ hτ) z J =
          (wVal w z J J' (r ≫ (snd T A).left) ^ a * wVal w z J J' (r ≫ m.left) ^ (-b)) * val α r z J')
    {s₀ s₀' s s'} (hs : SecRel hp τ hτ w s s₀) (hs' : SecRel hp τ hτ w s' s₀')
    (H₁ : IsTwistPull A L₁ (lift (fst T A) m) m (lift_snd _ _) a b α s s') :
    IsTwistPull G L₀ (lift (fst T₀ G) m₀) m₀ (lift_snd _ _) a b α₀ s₀ s₀' := by
  obtain ⟨χ, -, h₂⟩ := exists_psi_inv' hp τ hτ
  refine VVRank.isTwistPull_of_sv G hL₀ hα₀ fun y J hJ => ?_
  obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
  have q := VVRank.sv_of_isTwistPull A H₁ χ y hJ'
  have e : (χ ≫ (lift (fst T A) m).left) ≫ (snd T A).left = χ ≫ m.left := by
    rw [Category.assoc, ← Over.comp_left, lift_snd]
  rw [← h₂, hs' _ _ _ _ _ hJ hJ', H _ _ _ _ _ hJ hJ', Category.assoc, ← psi_lift hp τ hτ h, ← Category.assoc,
    hs _ _ _ _ _ hJ hJ', e, zpow_neg, q]
  simp only [Units.val_mul]
  rw [mul_right_comm _ _ (val α _ y J').val, _root_.mul_assoc (_ * _), Units.inv_mul_cancel_left, _root_.mul_assoc]
end GlobalTheory.ThetaPtUp
