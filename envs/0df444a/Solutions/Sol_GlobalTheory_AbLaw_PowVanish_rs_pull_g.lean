-- Prove2me | solution 1 for GlobalTheory.AbLaw.PowVanish.rs_pull_g
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:01.978473+00:00
-- url     : https://prove2.me/submissions/e92bd0dc-151a-4ebd-912c-5ed9306765c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesDescent
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_rs_pb
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_app_eq_pb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.PowVanish
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.AbLaw.PowVanish
theorem _root_.solution (M : LB X) (f : Y ⟶ X) (i j : M.ι) {W : Y.Opens}
    (e : W ≤ (M.pull f).U (fun _ => i) ⊓ (M.pull f).U (fun _ => j)) :
    rs Y e ((M.pull f).g (fun _ => i) (fun _ => j)).val =
      pb f (pre_pull M f i j e) (M.g i j).val := by
  change rs Y e (∏ _k : PUnit, (res _ (pullU f _ (M.g i j))) ^ (1 : ℤ)).val = _
  rw [Fintype.prod_unique, zpow_one]
  change rs Y e (rs Y _ ((f.app _).hom (M.g i j).val)) = _
  rw [app_eq_pb]
  exact (congrArg (rs Y e) (rs_pb f _ _ _)).trans (rs_pb f _ _ _)
end GlobalTheory.AbLaw.PowVanish
