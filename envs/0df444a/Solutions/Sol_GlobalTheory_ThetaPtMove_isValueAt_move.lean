-- Prove2me | solution 1 for GlobalTheory.ThetaPtMove.isValueAt_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:46:06.42286+00:00
-- url     : https://prove2.me/submissions/61044348-b088-4b28-996f-e27358d51dfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Theorems.Thm_GlobalTheory_ThetaPtMove_ptSecT_snd
import Theorems.Thm_GlobalTheory_ThetaPtMove_sv_of_isValueAt
import Theorems.Thm_GlobalTheory_ThetaPtMove_isValueAt_of_sv
import Theorems.Thm_GlobalTheory_ThetaPtMove_psi_ptSec
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
theorem _root_.solution (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} {x : T ⟶ A} {x₀ : T₀ ⟶ G}
    (hx : τ ≫ x₀.left = x.left ≫ φ)
    {ρ₀ : LB.Gen (LB.LinComb L₀ (Y := T₀.left) (K := Fin 1) (fun _ => x₀.left) (fun _ => a))}
    {ρ : LB.Gen (LB.LinComb L₁ (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))}
    (H : GenThrough w _ _ _ ρ ρ₀ τ) {s₀ s} (hs : SecRel hp τ hτ w s s₀) {c : Γ(T₀.left, ⊤)}
    (H₀ : IsValueAt G L₀ a s₀ x₀ ρ₀ c) : IsValueAt A L₁ a s x ρ (τ.appTop.hom c) := by
  refine isValueAt_of_sv hL₁ fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' hL₀ y
  have q := sv_of_isValueAt H₀ (𝟙 _ ≫ τ) y hJ
  rw [H _ _ _ _ _ hJ hJ', Category.assoc, ← psi_ptSec hp τ hτ hx, ← Category.assoc, hs _ _ _ _ _ hJ hJ',
    Category.assoc, ptSecT_snd, Fin.prod_univ_one, Units.val_mul, mul_left_comm] at q
  exact ((Units.mul_right_inj _).1 q).trans (congrArg (· * _) (gs_pull (𝟙 _) τ y ⊤ trivial c).symm)
end GlobalTheory.ThetaPtMove
