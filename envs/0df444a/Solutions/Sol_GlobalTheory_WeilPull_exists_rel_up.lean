-- Prove2me | solution 1 for GlobalTheory.WeilPull.exists_rel_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:45:34.514347+00:00
-- url     : https://prove2.me/submissions/a8b658ec-0ae4-4ff7-bb5a-316da431a3dd

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
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
theorem _root_.solution [IsIso τ] (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen)
    (x₀ : T₀ ⟶ G) (θ : ThetaGrp A L₁ k T) (hx : τ ≫ x₀.left = θ.pt.left ≫ φ) :
    ∃ θ₀ : ThetaGrp G L₀ k T₀, θ₀.pt = x₀ ∧ Rel hp τ hτ w θ θ₀ := by
  obtain ⟨χ, h₁, h₂⟩ := exists_psi_inv hp τ hτ
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hL₀ hL₁
    (φ' := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ θ.isGen
  have e₀ : χ ≫ (snd T A).left ≫ φ = (snd T₀ G).left := by
    rw [← psi_snd hp τ hτ, ← Category.assoc, h₂, Category.id_comp]
  have e₁ : χ ≫ (translPt A θ.pt).left ≫ φ = (translPt G x₀).left := by
    rw [← psi_tr hp τ hτ _ _ hx, ← Category.assoc, h₂, Category.id_comp]
  obtain ⟨u, hu, hu'⟩ := exists_gen hL₀ (φ' := ![(snd T₀ G).left, (translPt G x₀).left]) (ε' := ![k, -k])
    (fun U _ g => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => g q ^ k) e₀
      · exact congrArg (fun q => g q ^ (-k)) e₁)
    (LB.pullGen L₀ _ _ t χ) (DVR.pullGen_isGen _ _ _ _ ht _)
  refine ⟨⟨x₀, u, hu⟩, rfl, fun Z r z J₀ J hG hJ => ?_⟩
  have e : (r ≫ (psiO hp τ hτ).left) ≫ χ = r := by
    rw [Category.assoc]; exact (congrArg (r ≫ ·) h₁).trans (Category.comp_id _)
  refine ((hu' Z _ z J₀ hG).trans ((val_pull hG _ _ _).trans (congrArg (fun q => val t q z J₀) e))).trans ?_
  refine (hv Z r z _ _ (hG.mem _ r) (hJ.mem _ r)).trans ?_
  congr 1
  simp only [pw, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.assoc]
end GlobalTheory.WeilPull
