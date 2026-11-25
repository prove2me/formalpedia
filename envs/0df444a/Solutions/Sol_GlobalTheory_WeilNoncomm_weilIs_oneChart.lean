-- Prove2me | solution 1 for GlobalTheory.WeilNoncomm.weilIs_oneChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:31:57.834803+00:00
-- url     : https://prove2.me/submissions/4883848f-a5bf-440b-ac57-f5a5cd4fb1a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NotWeilIsGrpPullbackNoncomm
import Theorems.Thm_GlobalTheory_WeilNoncomm_gm_neg_one
import Theorems.Thm_GlobalTheory_WeilNoncomm_oneChart_isLB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_of_gm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_val_constGen


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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.WeilNoncomm
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
namespace GlobalTheory.WeilNoncomm
theorem _root_.solution {T : Over S} (k : ℤ) (x y : T ⟶ G)
    (hu : ∀ u : Γ((overRes (T := T) ⊤ ⊗ G).left, ⊤)ˣ, u = 1 ∨ u = -1) : WeilIs G (oneChart G.left) k x y 1 := by
  intro p
  have ex : ∀ a : overRes (T := T) ⊤ ⟶ G, ∃ θ : ThetaGrp G (oneChart G.left) k (overRes (T := T) ⊤), θ.pt = a :=
    fun a => ⟨⟨a, ⟨fun _ => 1⟩, isGen_of_gm _ fun y j j' _ _ => by
      have : trF (L := oneChart G.left) ![(snd (overRes (T := T) ⊤) G).left, (translPt G a).left] ![k, -k] (𝟙 _) y j j' = 1 :=
        Finset.prod_eq_one fun i _ => (congrArg (· ^ _) (map_one _)).trans (one_zpow _)
      exact (map_one _).trans ((congrArg₂ (· * ·) this (map_one _)).trans (_root_.one_mul _)).symm⟩, rfl⟩
  obtain ⟨a, ha⟩ := ex (overResι ⊤ ≫ x)
  obtain ⟨b, hb⟩ := ex (overResι ⊤ ≫ y)
  refine ⟨⊤, trivial, ⟨a, b, ha, hb⟩, fun θx θy _ _ => corr_of_val (oneChart_isLB _) fun z J hJ => ?_⟩
  have sg : ∀ θ : ThetaGrp G (oneChart G.left) k (overRes (T := T) ⊤), ∃ e, ∀ r, val θ.φ r z J = e := fun θ => by
    have le : (⊤ : (overRes (T := T) ⊤ ⊗ G).left.Opens) ≤ LB.wchart (oneChart G.left)
        ![(snd (overRes (T := T) ⊤) G).left, (translPt G θ.pt).left] (fun _ => PUnit.unit) :=
      fun _ _ => Set.mem_iInter.2 fun _ => trivial
    have e : ∀ r, val θ.φ r z J = gm r z ⊤ (res le (θ.φ.s fun _ => PUnit.unit)) := fun r =>
      (gm_res r z le trivial _).symm
    rcases hu (res le (θ.φ.s fun _ => PUnit.unit)) with h | h
    · exact ⟨1, fun r => (e r).trans ((congrArg _ h).trans (map_one _))⟩
    · exact ⟨-1, fun r => (e r).trans ((congrArg _ h).trans (gm_neg_one _ _ _ trivial))⟩
  obtain ⟨e, he⟩ := sg θx
  obtain ⟨e', he'⟩ := sg θy
  refine ((val_mul hJ _ _ _).trans (congrArg (val θx.φ (𝟙 _) z J * ·) (val_pull hJ _ _ _))).trans
    (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg (val θy.φ (𝟙 _) z J * ·) (val_pull hJ _ _ _))) (val_constGen _ _ _ _ _))).symm)
  have u : unitRes (T := T) ⊤ 1 = 1 := map_one _
  rw [he, he', he, he', u, map_one, _root_.mul_one, mul_comm]
end GlobalTheory.WeilNoncomm
