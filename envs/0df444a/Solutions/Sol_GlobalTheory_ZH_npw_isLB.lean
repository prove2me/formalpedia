-- Prove2me | solution 1 for GlobalTheory.ZH.npw_isLB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:17:52.069837+00:00
-- url     : https://prove2.me/submissions/fefd158a-889f-435b-ae4d-b062bf5dcb71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB

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
theorem _root_.solution {X : Scheme.{0}} {H : LB X} (hH : H.IsLB) (d : ℕ) : (npw H d).IsLB where
  cover := hH.cover
  g_self i := (map_pow _ _ _).trans ((congrArg (· ^ d) (hH.g_self i)).trans (one_pow d))
  cocycle i j l := by
    refine (congrArg₂ (· * ·) (map_pow _ _ _) (map_pow _ _ _)).trans ((mul_pow _ _ _).symm.trans
      ((congrArg (· ^ d) (hH.cocycle i j l)).trans (map_pow _ _ _).symm))
end GlobalTheory.ZH
