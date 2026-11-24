-- Prove2me | solution 1 for GlobalTheory.UU.SecMod.sval_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:43:29.540948+00:00
-- url     : https://prove2.me/submissions/fe59005d-f75e-479c-b0a0-970d39d74c73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SmulOneSecEqZeroIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_FinrankComplexReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.UU
open GlobalTheory.UU.SecMod
variable {F : Type} [CommRing F] {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of F)} {N : LB Y}
variable {X Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
  {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (r : Z ⟶ Y)
include hJ
namespace GlobalTheory.UU.SecMod
theorem _root_.solution : sval (0 : SecMod p (LB.LinComb L φ ε)).sec r z J = 0 :=
  (gs_eq r z _ (hJ.mem φ r) _).trans (by erw [map_zero, map_zero])
end GlobalTheory.UU.SecMod
