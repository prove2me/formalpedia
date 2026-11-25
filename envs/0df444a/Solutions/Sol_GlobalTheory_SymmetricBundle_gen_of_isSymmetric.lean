-- Prove2me | solution 1 for GlobalTheory.SymmetricBundle.gen_of_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:50:32.419651+00:00
-- url     : https://prove2.me/submissions/6dfe994b-3b35-4ffc-ba86-3e5399da481c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSymmetricIffExistsGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.SymmetricBundle
open Geo.Tor
namespace GlobalTheory.SymmetricBundle
theorem _root_.solution {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (h : L.IsSymmetric) :
    ∃ s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]), s.IsGen ∧
      LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec G)) (LB.oneGen L.L) := by
  obtain ⟨he, w, hw, hm⟩ := h
  have oi : eSec G ≫ (ι[G]).left = eSec G := he.trans (Category.id_comp _)
  have pg := (isGen_iff w).1 hw
  have pm := (maps_iff w (K := PUnit) (fun _ => eSec G) (fun _ => eSec G) (fun _ => 1) L.rig L.rig (𝟙 _) _
    (fun j => rigPull_le _ (𝟙 _) he L.L j) (fun _ => rfl)).1 hm
  have m₀ : ∀ (j : Fin 2 → L.L.ι) (x : G.left), x ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j →
      (ι[G]).left x ∈ L.L.U (j 0) := fun j x hx => Set.mem_iInter.1 hx 0
  have m₁ : ∀ (j : Fin 2 → L.L.ι) (x : G.left), x ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j →
      x ∈ L.L.U (j 1) := fun j x hx => Set.mem_iInter.1 hx 1
  have le : ∀ j : Fin 2 → L.L.ι, LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j ≤
      (L.L.pull (ι[G]).left).U (fun _ => j 0) ⊓ L.L.U (j 1) := fun j x hx => ⟨mem_pull.2 (m₀ j x hx), m₁ j x hx⟩
  let s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]) :=
    ⟨fun j => res (le j) (w.s (fun _ => j 0, j 1))⟩
  have hs : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (j : Fin 2 → L.L.ι),
      f y ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j →
      gm f y (LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j) (s.s j) = gw w f y (j 0) (j 1) :=
    fun Y f y j hj => gm_res f y (le j) hj _
  refine ⟨s, fun j j' => unit_ext fun x hx => ?_, corr_of_val L.isLB fun y J hJ => ?_⟩
  · refine ((gm_res (𝟙 G.left) x _ hx _).trans (hs _ (𝟙 G.left) x j hx.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_linComb L.L _ _ (𝟙 _) x j j' hx.1 hx.2)
        ((gm_res (𝟙 G.left) x _ hx _).trans (hs _ (𝟙 G.left) x j' hx.2)))).symm)
    rw [pg _ (𝟙 _) x (j 0) (j' 0) (j 1) (j' 1) (m₀ _ _ hx.1) (m₀ _ _ hx.2) (m₁ _ _ hx.1) (m₁ _ _ hx.2),
      Fin.prod_univ_two]
    congr 1
    show _ = gm (𝟙 _ ≫ (ι[G]).left) x _ (L.L.g (j 0) (j' 0)) ^ (1 : ℤ) *
      gm (𝟙 _ ≫ 𝟙 _) x _ (L.L.g (j 1) (j' 1)) ^ (-1 : ℤ)
    rw [Category.comp_id, zpow_one, zpow_neg_one]
  · have ri : (𝟙 _ ≫ eSec G) ≫ (ι[G]).left = 𝟙 _ ≫ eSec G := by rw [Category.assoc, oi]
    have hq₀ : (𝟙 _ ≫ eSec G) y ∈ L.L.U (J (𝟙 _ ≫ eSec G)) := hJ _
    have hq₁ : (ι[G]).left ((𝟙 _ ≫ eSec G) y) ∈ L.L.U (J (𝟙 _ ≫ eSec G)) := by
      have := hJ ((𝟙 _ ≫ eSec G) ≫ (ι[G]).left)
      rw [congrArg J ri] at this
      exact this
    rw [val_pull hJ, val_one, val_of s (𝟙 _ ≫ eSec G) y J ![J (𝟙 _ ≫ eSec G), J (𝟙 _ ≫ eSec G)] (fun k => by
      fin_cases k
      · exact congrArg J ri
      · exact congrArg J (Category.comp_id _)), hs _ _ _ _ (Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [hq₁, hq₀])]
    have a := pm _ (𝟙 _) y (fun _ => J (𝟙 _ ≫ eSec G)) (fun _ => J (𝟙 _ ≫ eSec G)) (fun _ => hq₁) (fun _ => hq₀)
    rw [Category.comp_id, Fintype.prod_unique, zpow_one] at a
    exact mul_eq_right.1 a.symm
end GlobalTheory.SymmetricBundle
