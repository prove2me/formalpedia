-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeOpen.triv_pull_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:03.303594+00:00
-- url     : https://prove2.me/submissions/0ea24f33-ecba-4c40-864d-96a56e2139fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeOpen
namespace GlobalTheory.AbLaw.CubeOpen
theorem _root_.solution {X Y Z : Scheme.{0}} {M : LB X} (f : Y ⟶ X) (h : Z ⟶ Y)
    (ht : Triv (M.pull (h ≫ f))) : Triv ((M.pull f).pull h) := by
  obtain ⟨t, ht⟩ := ht
  have hle : ∀ j : PUnit.{1} → PUnit.{1} → M.ι,
      LB.wchart (M.pull f) (K := PUnit) (fun _ => h) j ≤
        LB.wchart M (K := PUnit) (fun _ => h ≫ f) (j PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun k =>
      Set.mem_iInter.1 (Set.mem_iInter.1 hy PUnit.unit) k
  refine ⟨⟨fun j => res (hle j) (LB.ts t (j PUnit.unit))⟩, (LB.isGen_iff _ _).2 fun i j => ?_⟩
  have key := congrArg (res (inf_le_inf (hle i) (hle j)))
    ((LB.isGen_iff M t).1 ht (i PUnit.unit) (j PUnit.unit))
  rw [LB.lcg_comp M (fun _ : PUnit.{1} => f) (fun _ => 1) h (i PUnit.unit) (j PUnit.unit)] at key
  erw [map_mul] at key
  simp only [LB.res_res] at key
  rw [LB.lcg_pull]
  change res _ (res (hle i) _) = _ * res _ (res (hle j) _)
  simp only [LB.res_res]
  exact key
end GlobalTheory.AbLaw.CubeOpen
