-- Prove2me | solution 1 for GlobalTheory.Cartier.SecMaps.isRegularSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:36:14.01283+00:00
-- url     : https://prove2.me/submissions/27619512-cbc1-4e3d-ade8-4b64c2a6856e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_of_isUnit
import Theorems.Thm_GlobalTheory_Cartier_isRegularFn_of_locally
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_mem_of_cover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.Cartier
namespace SecMaps
theorem _root_.solution {A B : LB X} (hA : A.IsLB) {w : LB.Iso A B} {a : A.Sec} {b : B.Sec}
    (h : SecMaps w a b) (ha : IsRegularSec a) : IsRegularSec b := fun p =>
  isRegularFn_of_locally fun x hx => by
    obtain ⟨q, hq⟩ := LB.mem_of_cover hA x
    refine ⟨B.U p ⊓ A.U q, inf_le_left, ⟨hx, hq⟩, ?_⟩
    rw [h (p, q)]
    exact (IsRegularFn.of_isUnit (Units.isUnit _)).mul ((ha q).resG _)
end SecMaps
end GlobalTheory.Cartier
