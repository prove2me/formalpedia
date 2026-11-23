-- Prove2me | solution 1 for GlobalTheory.Cartier.SecMaps.unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:07.640604+00:00
-- url     : https://prove2.me/submissions/11f92d7a-f503-4de2-a39b-472df8934fb1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul_right_cancel

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
theorem _root_.solution {A B : LB X} {w w' : LB.Iso A B} {a : A.Sec} {b : B.Sec}
    (h : SecMaps w a b) (h' : SecMaps w' a b) (ha : IsRegularSec a) : w = w' := by
  obtain ⟨w⟩ := w
  obtain ⟨w'⟩ := w'
  congr 1
  funext p
  exact Units.ext (((ha p.2).resG inf_le_right).mul_right_cancel ((h p).symm.trans (h' p)))
end SecMaps
end GlobalTheory.Cartier
