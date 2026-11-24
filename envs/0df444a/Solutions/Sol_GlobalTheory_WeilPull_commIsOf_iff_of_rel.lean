-- Prove2me | solution 1 for GlobalTheory.WeilPull.commIsOf_iff_of_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:28:11.333534+00:00
-- url     : https://prove2.me/submissions/ddd7bf0a-63d8-42ec-9b70-e59a80009cd1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Theorems.Thm_GlobalTheory_WeilPull_exists_psi_inv
import Theorems.Thm_GlobalTheory_WeilPull_transl_commute
import Theorems.Thm_GlobalTheory_WeilPull_cancel_iff
import Theorems.Thm_GlobalTheory_CommPairing_commIsOf_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_psi_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_psi_transl


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
theorem _root_.solution [IsIso τ] (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ))
    {θx θy : ThetaGrp A L₁ k T} {θx₀ θy₀ : ThetaGrp G L₀ k T₀} (hc : θx.pt * θy.pt = θy.pt * θx.pt)
    (hx : τ ≫ θx₀.pt.left = θx.pt.left ≫ φ) (hy : τ ≫ θy₀.pt.left = θy.pt.left ≫ φ)
    (mx : Rel hp τ hτ w θx θx₀) (my : Rel hp τ hτ w θy θy₀) (c₀ : Γ(T₀.left, ⊤)ˣ) (c : Γ(T.left, ⊤)ˣ)
    (hcc : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z), gm (r ≫ τ) z ⊤ c₀ = gm r z ⊤ c) :
    CommIsOf A L₁ k θx θy c ↔ CommIsOf G L₀ k θx₀ θy₀ c₀ := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J₀) (J), Good L₀ z J₀ → Good L₁ z J →
      (tval θx₀ (r ≫ (psiO hp τ hτ).left) z J₀ *
          tval θy₀ ((r ≫ (psiO hp τ hτ).left) ≫ (translT G θx₀.pt).left) z J₀ =
        tval θy₀ (r ≫ (psiO hp τ hτ).left) z J₀ *
          tval θx₀ ((r ≫ (psiO hp τ hτ).left) ≫ (translT G θy₀.pt).left) z J₀ *
          gm ((r ≫ (psiO hp τ hτ).left) ≫ (fst T₀ G).left) z ⊤ c₀ ↔
      tval θx r z J * tval θy (r ≫ (translT A θx.pt).left) z J =
        tval θy r z J * tval θx (r ≫ (translT A θy.pt).left) z J * gm (r ≫ (fst T A).left) z ⊤ c) := by
    intro Z r z J₀ J hG hJ
    have t : ∀ (x : T ⟶ A) (x₀ : T₀ ⟶ G), τ ≫ x₀.left = x.left ≫ φ →
        (r ≫ (psiO hp τ hτ).left) ≫ (translT G x₀).left = (r ≫ (translT A x).left) ≫ (psiO hp τ hτ).left :=
      fun x x₀ h => by rw [Category.assoc, Category.assoc, psi_transl hp τ hτ _ _ h]
    have g : gm ((r ≫ (psiO hp τ hτ).left) ≫ (fst T₀ G).left) z ⊤ c₀ = gm (r ≫ (fst T A).left) z ⊤ c := by
      rw [Category.assoc, psi_fst, ← Category.assoc, hcc]
    have s : ∀ x : T ⟶ A, (r ≫ (translT A x).left) ≫ (snd T A).left = r ≫ (translPt A x).left := fun x => by
      rw [Category.assoc, ← Over.comp_left, translT, lift_snd]
    have q : (r ≫ (translT A θx.pt).left) ≫ (translPt A θy.pt).left =
        (r ≫ (translT A θy.pt).left) ≫ (translPt A θx.pt).left := by
      rw [Category.assoc, Category.assoc, transl_commute hc]
    rw [t _ _ hx, t _ _ hy, g, mx Z _ z J₀ J hG hJ, mx Z _ z J₀ J hG hJ, my Z _ z J₀ J hG hJ, my Z _ z J₀ J hG hJ,
      s, s, q]
    simp only [zpow_neg]
    exact cancel_iff _ _ _ _ _ _ _ _ _
  rw [commIsOf_iff hL₀, commIsOf_iff hL₁]
  constructor
  · intro H Z r₀ z J₀ hG
    obtain ⟨χ, -, h₂⟩ := exists_psi_inv hp τ hτ
    choose J hJ using fun ψ : Z ⟶ A.left => exists_chart hL₁ (ψ z)
    have e : (r₀ ≫ χ) ≫ (psiO hp τ hτ).left = r₀ := by rw [Category.assoc, h₂, Category.comp_id]
    have := (key Z (r₀ ≫ χ) z J₀ J hG hJ).2 (H Z _ z J hJ)
    rwa [e] at this
  · intro H Z r z J hJ
    choose J₀ hG using fun ψ : Z ⟶ G.left => exists_chart hL₀ (ψ z)
    exact (key Z r z J₀ J hG hJ).1 (H Z _ z J₀ hG)
end GlobalTheory.WeilPull
