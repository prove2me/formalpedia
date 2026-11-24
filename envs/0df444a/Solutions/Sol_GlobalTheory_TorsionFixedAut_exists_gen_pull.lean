-- Prove2me | solution 1 for GlobalTheory.TorsionFixedAut.exists_gen_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:33:07.160865+00:00
-- url     : https://prove2.me/submissions/5af58fef-6356-4d7b-87c3-23f464f31124

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion
import Theorems.Thm_GlobalTheory_TorsionFixedAut_isGen_of_germs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
noncomputable section
open GlobalTheory GlobalTheory.TorsionFixedAut
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
variable {σ : X ⟶ X} (c : LB.Gen (LB.LinComb L (K := Fin 2) ![σ, 𝟙 X] ![1, -1]))
namespace GlobalTheory.TorsionFixedAut
theorem _root_.solution (M : LB X) (t : LB.Gen M) (ht : t.IsGen) (f : Y ⟶ X) :
    ∃ u : LB.Gen (M.pull f), u.IsGen := by
  refine ⟨⟨fun j => res (LB.wchart_le M (fun _ : PUnit => f) j PUnit.unit) (pullU f _ (t.s (j PUnit.unit)))⟩,
    isGen_of_germs _ fun y j j' hj hj' => ?_⟩
  have v : ∀ j : PUnit → M.ι, y ∈ LB.wchart M (fun _ : PUnit => f) j →
      gm (𝟙 Y) y (LB.wchart M (fun _ : PUnit => f) j)
        (res (LB.wchart_le M (fun _ : PUnit => f) j PUnit.unit) (pullU f _ (t.s (j PUnit.unit)))) =
      gm (𝟙 Y ≫ f) y _ (t.s (j PUnit.unit)) := fun j hj =>
    (gm_res _ y _ hj _).trans (gm_pull _ f y _ (Set.mem_iInter.1 hj PUnit.unit) _)
  refine (v j hj).trans (Eq.trans ?_ (congrArg _ (v j' hj')).symm)
  have hm : (𝟙 Y ≫ f) y ∈ M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit) :=
    ⟨Set.mem_iInter.1 hj PUnit.unit, Set.mem_iInter.1 hj' PUnit.unit⟩
  rw [trF, Fintype.prod_unique, zpow_one]
  exact (gm_res _ y _ hm _).symm.trans ((congrArg (gm _ y _) (ht _ _)).trans ((map_mul _ _ _).trans
    (congrArg _ (gm_res _ y _ hm _))))
end GlobalTheory.TorsionFixedAut
