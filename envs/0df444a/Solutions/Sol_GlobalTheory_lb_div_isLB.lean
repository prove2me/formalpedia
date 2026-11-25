-- Prove2me | solution 1 for GlobalTheory.lb_div_isLB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:32:40.784801+00:00
-- url     : https://prove2.me/submissions/cdfb7e55-6878-4688-96eb-bb4ee648d429

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {I : Type} [SmallCategory I] [IsCofiltered I]
variable (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
namespace GlobalTheory
theorem _root_.solution {Y : Scheme.{0}} {M N : LB Y} (hM : M.IsLB) (hN : N.IsLB) : (LB.div N M).IsLB where
  cover := top_le_iff.1 fun y _ => by
    obtain ⟨i, hi⟩ := exists_chart hN y
    obtain ⟨j, hj⟩ := exists_chart hM y
    exact Opens.mem_iSup.2 ⟨(i, j), hi, hj⟩
  g_self p := unit_ext fun y hy => by
    refine (gm_res (𝟙 Y) y _ hy _).trans ((gm_div M N (𝟙 Y) y p p ⟨hy, hy⟩).trans ?_)
    rw [gm_self hN _ y hy.1, gm_self hM _ y hy.2, map_one, inv_one, mul_one]
  cocycle p q r := unit_ext fun y hy => by
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res (𝟙 Y) y _ hy _).trans (gm_div M N (𝟙 Y) y p q hy.1))
      ((gm_res (𝟙 Y) y _ hy _).trans (gm_div M N (𝟙 Y) y q r ⟨hy.1.2, hy.2⟩)))).trans
      (Eq.trans ?_ ((gm_res (𝟙 Y) y _ hy _).trans (gm_div M N (𝟙 Y) y p r ⟨hy.1.1, hy.2⟩)).symm)
    rw [← gm_cocycle hN (𝟙 Y) y hy.1.1.1 hy.1.2.1 hy.2.1, ← gm_cocycle hM (𝟙 Y) y hy.1.1.2 hy.1.2.2 hy.2.2,
      mul_inv, mul_mul_mul_comm]
end GlobalTheory
