-- Prove2me | solution 1 for GlobalTheory.SelfCube.prod_finset_fin_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:09.295328+00:00
-- url     : https://prove2.me/submissions/e90fe5d3-7237-4ede-8bf8-3364db70f953

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.SelfCube
namespace GlobalTheory.SelfCube
theorem _root_.solution (f : Finset (Fin 2) → ℂ) :
    ∏ I : ULift.{0} (Finset (Fin 2)), f I.down = f ∅ * f {0} * f {1} * f {0, 1} := by
  rw [Fintype.prod_equiv Equiv.ulift (fun I : ULift.{0} (Finset (Fin 2)) => f I.down) f (fun _ => rfl)]
  rw [← Finset.powerset_univ, show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide,
    Finset.prod_powerset_insert (by decide),
    show ({1} : Finset (Fin 2)).powerset = {∅, {1}} by decide,
    Finset.prod_pair (by decide), Finset.prod_pair (by decide)]
  have h0 : (insert (0 : Fin 2) (∅ : Finset (Fin 2))) = {0} := by decide
  rw [h0]
  ring
end GlobalTheory.SelfCube
