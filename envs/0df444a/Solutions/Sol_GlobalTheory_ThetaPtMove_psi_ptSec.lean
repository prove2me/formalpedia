-- Prove2me | solution 1 for GlobalTheory.ThetaPtMove.psi_ptSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:15:22.260411+00:00
-- url     : https://prove2.me/submissions/36bb6af9-2c46-4dbe-a7e2-b9aaa4e10971

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Theorems.Thm_GlobalTheory_ThetaPtMove_ptSecT_snd
import Theorems.Thm_GlobalTheory_ThetaPtMove_ptSecT_fst
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
theorem _root_.solution {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) :
    (ptSecT A x).left ≫ psi hp τ hτ = τ ≫ (ptSecT G x₀).left := by
  refine psi_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, psi_fst', ptSecT_fst, ← Category.assoc, ptSecT_fst, Category.id_comp,
      Category.comp_id]
  · rw [Category.assoc, Category.assoc, psi_snd', ptSecT_snd, ← Category.assoc, ptSecT_snd, hx]
end GlobalTheory.ThetaPtMove
