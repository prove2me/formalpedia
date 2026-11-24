-- Prove2me | solution 1 for GlobalTheory.ZH.FibPre.H_isLB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:38:37.234794+00:00
-- url     : https://prove2.me/submissions/3db22ab2-b7ed-40c9-9a84-fefe449d1da1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Theorems.Thm_GlobalTheory_ZH_npw_isLB
import Theorems.Thm_GlobalTheory_ZH_pullChart_isLB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
attribute [instance] FibPre.grp FibPre.comm
namespace GlobalTheory.ZH
namespace FibPre
theorem _root_.solution {k : Type} [Field k] (Φ : FibPre k) (d : ℕ) : (Φ.H d).IsLB :=
  npw_isLB (pullChart_isLB Φ.D.q.left Φ.isLB) d
end FibPre
end GlobalTheory.ZH
