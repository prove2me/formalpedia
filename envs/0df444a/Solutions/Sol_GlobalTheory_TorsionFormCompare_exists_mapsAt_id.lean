-- Prove2me | solution 1 for GlobalTheory.TorsionFormCompare.exists_mapsAt_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:52:46.56664+00:00
-- url     : https://prove2.me/submissions/8083c0e3-0088-40b9-a0af-707d2803f0eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatIsoUnitGenerator
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatTorsionIsomorphism
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIdentityPullbackDegeneration
import Theorems.Thm_GlobalTheory_TorsionFormCompare_exists_gen_of_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gw_isoPullId
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TorsionFormCompare
namespace GlobalTheory.TorsionFormCompare
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X) (p : Y ⟶ X) (n : ℤ)
    (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) (ha : a.IsGen) :
    ∃ b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p ≫ F) (fun _ => n)),
      GeneratorPullback.MapsAt L L (J := PUnit) (fun _ => F) (isoPullId (idIso L) hF) p n a b ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), val b r z J = val a r z J := by
  obtain ⟨b, hb, hv⟩ := exists_gen_of_eq L (q := p ≫ F) (p := p) (by rw [hF, Category.comp_id]) n a
  refine ⟨b, fun jN jL => unit_ext fun y hy => ?_, hv⟩
  have hL : p y ∈ L.U jL := hy.2
  have hN : p y ∈ L.U (jN PUnit.unit) := by
    have := mem_pull.1 hy.1
    rw [hF] at this
    exact this
  have m₁ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun _ : PUnit => p) jN := Set.mem_iInter.2 fun _ => hN
  have m₂ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun _ : PUnit => p) (fun _ => jL) := Set.mem_iInter.2 fun _ => hL
  refine (gm_res _ y _ hy _).trans ((hb _ _ y jN).trans ((gen_trans ha (𝟙 Y) y m₁ m₂).trans ?_))
  refine Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_zpow _ _ _).trans ?_) (gm_res _ y _ hy _)))
  rw [trF, Fintype.prod_unique]
  refine congrArg (· ^ n) ((gm_pull (𝟙 Y) p y _ hy _).trans ?_)
  exact gw_isoPullId (idIso L) hF (𝟙 Y ≫ p) y (jN PUnit.unit) jL hN hL
end GlobalTheory.TorsionFormCompare
