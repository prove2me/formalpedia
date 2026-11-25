-- Prove2me | solution 1 for GlobalTheory.ThetaPtMove.exists_secRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:55:48.489715+00:00
-- url     : https://prove2.me/submissions/07a175f0-f6f9-4a7f-adb3-fbc00f39247e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Theorems.Thm_P2M_GlobalTheory_ThetaPtMove_psi_snd__014c8d7c58c3
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
theorem _root_.solution (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} (s₀ : LB.Sec (LPow G L₀ a T₀)) :
    ∃ s, SecRel hp τ hτ w s s₀ := by
  have e : ∀ _ : Fin 1, (snd T A).left ≫ φ = psi hp τ hτ ≫ (snd T₀ G).left := fun _ => (psi_snd' hp τ hτ).symm
  obtain ⟨s, hs⟩ := exists_secThrough (φ' := fun _ : Fin 1 => (snd T A).left) (φ := fun _ => (snd T₀ G).left)
    (ε := fun _ => a) hw hL₀ hL₁ e s₀
  refine ⟨s, fun Z r z J J' hJ hJ' => (hs.sval e r hJ hJ').trans ?_⟩
  rw [Fin.prod_univ_one]
end GlobalTheory.ThetaPtMove
