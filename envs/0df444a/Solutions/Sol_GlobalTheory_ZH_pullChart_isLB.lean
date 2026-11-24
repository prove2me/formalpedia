-- Prove2me | solution 1 for GlobalTheory.ZH.pullChart_isLB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:18.63238+00:00
-- url     : https://prove2.me/submissions/22a62542-9019-4b58-a928-c9388009d6ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Theorems.Thm_GlobalTheory_ZH_pullU_res_eq

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
theorem _root_.solution {X Y : Scheme.{0}} (f : Y ⟶ X) {L : LB X} (hL : L.IsLB) :
    (⟨L.ι, fun l => f ⁻¹ᵁ L.U l, fun l l' => pullU f (L.U l ⊓ L.U l') (L.g l l')⟩ : LB Y).IsLB := by
  refine ⟨?_, fun i => ?_, fun i j l => ?_⟩
  · show ⨆ l, f ⁻¹ᵁ L.U l = ⊤
    rw [← Scheme.Hom.preimage_iSup, hL.cover, Scheme.Hom.preimage_top]
  · have e := congrArg (pullU f _) (hL.g_self i)
    rw [map_one, pullU_res_eq] at e
    exact e
  · have e := congrArg (pullU f _) (hL.cocycle i j l)
    rw [map_mul, pullU_res_eq, pullU_res_eq, pullU_res_eq] at e
    exact e
end GlobalTheory.ZH
