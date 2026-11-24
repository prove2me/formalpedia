-- Prove2me | solution 1 for GlobalTheory.CubeValues.comp_foldr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:02:42.290203+00:00
-- url     : https://prove2.me/submissions/77b81ebd-53f1-4c23-83be-73bc1cd9e348

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace

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
open GlobalTheory GlobalTheory.CubeValues
variable {A : Over (Sp ℂ)} [GrpObj A] {L₀ : LB A.left} {g : ℕ} (u : HolUnif A L₀ g)
namespace GlobalTheory.CubeValues
theorem _root_.solution {T T' : Over (Sp ℂ)} (p : T' ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A)) (l : List (Fin n)) :
    p ≫ l.foldr (fun k acc => padd A (y k) acc) (pzero A T) = (l.map fun k => p ≫ y k).prod := by
  induction l with
  | nil =>
    simp only [List.foldr_nil, List.map_nil, List.prod_nil, pzero, Hom.one_def, comp_toUnit_assoc]
  | cons k l ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, ← ih, padd, Hom.mul_def, comp_lift_assoc]
end GlobalTheory.CubeValues
