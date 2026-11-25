-- Prove2me | solution 1 for GlobalTheory.SymmetricBundle.isSymmetric_of_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:52:10.126365+00:00
-- url     : https://prove2.me/submissions/a6bb82e3-00d7-4e84-9d61-bfb6cca6aff7

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
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
    (sy : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hsy : sy.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sy (eSec G)) (LB.oneGen L.L)) : L.IsSymmetric := by
  have oi : eSec G ≫ (ι[G]).left = eSec G := by
    have : η[G] ≫ ι[G] = η[G] := by simp
    exact congrArg (fun q => q.left) this
  have mem : ∀ (x : G.left) (a b : L.L.ι), (ι[G]).left x ∈ L.L.U a → x ∈ L.L.U b →
      x ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![a, b] := fun x a b ha hb =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [ha, hb]
  have le : ∀ p : (PUnit → L.L.ι) × L.L.ι, (L.L.pull (ι[G]).left).U p.1 ⊓ L.L.U p.2 ≤
      LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![p.1 PUnit.unit, p.2] := fun p x hx =>
    mem x _ _ (mem_pull.1 hx.1) hx.2
  let w : LB.Iso L.L (L.L.pull (ι[G]).left) := ⟨fun p => res (le p) (sy.s ![p.1 PUnit.unit, p.2])⟩
  have hw : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (a b : L.L.ι), (ι[G]).left (f y) ∈ L.L.U a → f y ∈ L.L.U b →
      gw w f y a b = gm f y (LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![a, b]) (sy.s ![a, b]) :=
    fun Y f y a b ha hb => gm_res f y (le (fun _ => a, b)) ⟨mem_pull.2 ha, hb⟩ _
  have pg : PGen w := by
    intro Y f y j j' k k' hj hj' hk hk'
    rw [hw Y f y j k hj hk, hw Y f y j' k' hj' hk', gen_trans hsy f y (mem _ _ _ hj hk) (mem _ _ _ hj' hk')]
    congr 1
    rw [trF, Fin.prod_univ_two]
    show gm (f ≫ (ι[G]).left) y _ (L.L.g j j') ^ (1 : ℤ) * gm (f ≫ 𝟙 _) y _ (L.L.g k k') ^ (-1 : ℤ) = _
    rw [Category.comp_id, zpow_one, zpow_neg_one]
  refine ⟨oi.trans (Category.id_comp _).symm, w, (isGen_iff w).2 pg, ?_⟩
  refine (maps_iff w (K := PUnit) (fun _ => eSec G) (fun _ => eSec G) (fun _ => 1) L.rig L.rig (𝟙 _) _
    (fun j => rigPull_le _ (𝟙 _) (oi.trans (Category.id_comp _).symm) L.L j) (fun _ => rfl)).2 ?_
  intro Z r z p q hp hq
  have hp₀ : (ι[G]).left ((r ≫ eSec G) z) ∈ L.L.U (p PUnit.unit) := hp PUnit.unit
  have hq₀ : (r ≫ eSec G) z ∈ L.L.U (q PUnit.unit) := hq PUnit.unit
  have ri : (r ≫ eSec G) ≫ (ι[G]).left = r ≫ eSec G := by rw [Category.assoc, oi]
  have hp₁ : (r ≫ eSec G) z ∈ L.L.U (p PUnit.unit) := by rw [← ri]; exact hp₀
  have hq₁ : (ι[G]).left ((r ≫ eSec G) z) ∈ L.L.U (q PUnit.unit) := by
    have := hq₀
    rw [← ri] at this; exact this
  have one : gw w (r ≫ eSec G) z (q PUnit.unit) (q PUnit.unit) = 1 := by
    obtain ⟨J, hJ, e⟩ := exists_good L.L L.isLB z (K := PUnit) (fun _ => r ≫ eSec G) q (fun _ _ _ => rfl)
      (fun _ => hq₀)
    have a := val_corr hJ hr r
    rw [val_pull hJ, val_one, val_of sy (r ≫ eSec G) z J ![q PUnit.unit, q PUnit.unit] (fun k => by
      fin_cases k
      · exact (congrArg J ri).trans (e PUnit.unit)
      · exact (congrArg J (Category.comp_id _)).trans (e PUnit.unit))] at a
    exact (hw _ _ _ _ _ hq₁ hq₀).trans a
  rw [Category.comp_id, Fintype.prod_unique, zpow_one,
    gen_trans L.rigGen r z (j := p) (j' := q) (Set.mem_iInter.2 fun _ => hp₁) (Set.mem_iInter.2 fun _ => hq₀)]
  congr 1
  have b := pg _ (r ≫ eSec G) z (p PUnit.unit) (q PUnit.unit) (q PUnit.unit) (q PUnit.unit) hp₀ hq₁ hq₀ hq₀
  rw [one, gm_self L.isLB _ z hq₀, ri, inv_one, _root_.mul_one, _root_.mul_one] at b
  rw [trF, Fintype.prod_unique, zpow_one]
  exact b.symm
end GlobalTheory.SymmetricBundle
