-- Prove2me | solution 1 for GlobalTheory.UU.lbIso_pw_pull_of_hasGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:11:46.264022+00:00
-- url     : https://prove2.me/submissions/8f1e5dc9-5f0a-4210-bdeb-8e37e639696a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulPullOfCubeOfSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LbIsoPwPullPowLocal
import Theorems.Thm_GlobalTheory_MulPull_HasGen_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
theorem _root_.solution {X : Scheme.{0}} {L : LB X} (F : X ⟶ X) (t : ℤ)
    (h : MulPull.HasGen L (K := Fin 2) ![F, 𝟙 X] ![1, -t]) : LBIso (pw L t) (L.pull F) := by
  obtain ⟨a, ha⟩ := h
  have mem : ∀ (x : X) (j k : L.ι), F x ∈ L.U j → x ∈ L.U k → x ∈ LB.wchart L ![F, 𝟙 X] ![j, k] :=
    fun x j k hj hk => Set.mem_iInter.2 fun i => by
      fin_cases i
      · exact hj
      · exact hk
  have le : ∀ p : (L.pull F).ι × L.ι,
      (L.pull F).U p.1 ⊓ L.U p.2 ≤ LB.wchart L ![F, 𝟙 X] ![p.1 PUnit.unit, p.2] :=
    fun p x hx => mem x _ _ (mem_pull.1 hx.1) hx.2
  let w : LB.Iso (pw L t) (L.pull F) := ⟨fun p => res (le p) (a.s _)⟩
  refine ⟨w, (isGen_iff w).2 fun Y r y j j' k k' hj hj' hk hk' => ?_⟩
  have e : ∀ j k, F (r y) ∈ L.U j → r y ∈ L.U k →
      gw w r y j k = gm r y (LB.wchart L ![F, 𝟙 X] ![j, k]) (a.s ![j, k]) := fun j k hj hk =>
    gm_res r y (le (fun _ => j, k)) ⟨mem_pull.2 hj, hk⟩ _
  rw [e j k hj hk, e j' k' hj' hk', gen_trans ha r y (mem _ _ _ hj hk) (mem _ _ _ hj' hk'), trF, Fin.prod_univ_two]
  congr 1
  show gm (r ≫ F) y _ (L.g j j') ^ (1 : ℤ) * gm (r ≫ 𝟙 X) y _ (L.g k k') ^ (-t) =
    gm (r ≫ F) y _ (L.g j j') * (gm r y (L.U k ⊓ L.U k') (L.g k k' ^ t))⁻¹
  rw [zpow_one, Category.comp_id, map_zpow, zpow_neg]
end GlobalTheory.UU
