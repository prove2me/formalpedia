-- Prove2me | solution 1 for GlobalTheory.ThetaPtMove.psi_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:04:55.551877+00:00
-- url     : https://prove2.me/submissions/cbcdcd9f-557b-45a1-8d78-4400491c7059

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
include hp hτ
namespace GlobalTheory.ThetaPtMove
theorem _root_.solution {m : T ⊗ A ⟶ A} {m₀ : T₀ ⊗ G ⟶ G} (h : psi hp τ hτ ≫ m₀.left = m.left ≫ φ) :
    (lift (fst T A) m).left ≫ psi hp τ hτ = psi hp τ hτ ≫ (lift (fst T₀ G) m₀).left := by
  have a₁ : (lift (fst T₀ G) m₀).left ≫ (fst T₀ G).left = (fst T₀ G).left := by rw [← Over.comp_left, lift_fst]
  have a₂ : (lift (fst T₀ G) m₀).left ≫ (snd T₀ G).left = m₀.left := by rw [← Over.comp_left, lift_snd]
  refine psi_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, psi_fst', a₁, psi_fst', ← Category.assoc, ← Over.comp_left, lift_fst]
  · rw [Category.assoc, Category.assoc, psi_snd', a₂, h, ← Category.assoc, ← Over.comp_left, lift_snd]
end GlobalTheory.ThetaPtMove
