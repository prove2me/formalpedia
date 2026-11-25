-- Prove2me | solution 1 for GlobalTheory.RigSq.gm_rig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:59:41.517925+00:00
-- url     : https://prove2.me/submissions/082ecde2-d57b-477c-9fc8-90a608eb470f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRescaleRigidifiedSquareIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.RigSq
variable {X Y : Scheme.{0}}
namespace GlobalTheory.RigSq
theorem _root_.solution {S : Scheme.{0}} {G : Over S} [GrpObj G] (R : RigLB G) (f : Y ⟶ (𝟙_ (Over S)).left) (y : Y)
    (j j' : R.L.ι) (hj : eSec G (f y) ∈ R.L.U j) (hj' : eSec G (f y) ∈ R.L.U j') :
    gm f y _ (R.rig.s (fun _ => j)) = gm (f ≫ eSec G) y _ (R.L.g j j') * gm f y _ (R.rig.s (fun _ => j')) := by
  have hp : f y ∈ (R.L.pull (eSec G)).U (fun _ => j) ⊓ (R.L.pull (eSec G)).U (fun _ => j') :=
    ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  have e := congrArg (gm f y _) (R.rigGen (fun _ => j) (fun _ => j'))
  rw [gm_res f y _ hp, map_mul, gm_res f y _ hp] at e
  refine e.trans (congrArg (· * _) ?_)
  show gm f y _ (∏ _k : PUnit, (res _ (pullU (eSec G) _ (R.L.g j j'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f (eSec G) y (R.L.U j ⊓ R.L.U j') ⟨hj, hj'⟩ _)
end GlobalTheory.RigSq
