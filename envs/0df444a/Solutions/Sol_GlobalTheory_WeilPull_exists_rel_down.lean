-- Prove2me | solution 1 for GlobalTheory.WeilPull.exists_rel_down
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:16:49.40056+00:00
-- url     : https://prove2.me/submissions/bdaaf28d-b219-44bd-a61f-09fccb431560

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_exists_theta_move
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_psi_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_psi_tr


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
open GlobalTheory GlobalTheory.WeilPull
open GlobalTheory.CommPairing
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {k : ℤ}
namespace GlobalTheory.WeilPull
theorem _root_.solution (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen)
    (x : T ⟶ A) (θ₀ : ThetaGrp G L₀ k T₀) (hx : τ ≫ θ₀.pt.left = x.left ≫ φ) :
    ∃ θ : ThetaGrp A L₁ k T, θ.pt = x ∧ Rel hp τ hτ w θ θ₀ := by
  obtain ⟨θ, rfl, m⟩ := exists_theta_move hp τ hτ hL₀ hL₁ w hw k x θ₀ hx
  refine ⟨θ, rfl, fun Z r z J₀ J hG hJ => ?_⟩
  have e₀ : (r ≫ (psiO hp τ hτ).left) ≫ (snd T₀ G).left = (r ≫ (snd T A).left) ≫ φ := by
    rw [Category.assoc, Category.assoc, psi_snd]
  have e₁ : (r ≫ (psiO hp τ hτ).left) ≫ (translPt G θ₀.pt).left = (r ≫ (translPt A θ.pt).left) ≫ φ := by
    rw [Category.assoc, Category.assoc, psi_tr hp τ hτ _ _ hx]
  have e : ∀ i, (r ≫ (psiO hp τ hτ).left) ≫ ![(snd T₀ G).left, (translPt G θ₀.pt).left] i =
      (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i) ≫ φ := fun i => by
    fin_cases i
    · exact e₀
    · exact e₁
  calc tval θ₀ (r ≫ (psiO hp τ hτ).left) z J₀ = _ :=
        m _ r z _ (fun i => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i)) (fun i => by
          show _ ∈ L₀.U (J₀ ((r ≫ (psiO hp τ hτ).left) ≫ _))
          rw [e i]; exact hG _) (fun i => hJ _)
    _ = _ := by
      congr 1
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [e₀, e₁]
end GlobalTheory.WeilPull
