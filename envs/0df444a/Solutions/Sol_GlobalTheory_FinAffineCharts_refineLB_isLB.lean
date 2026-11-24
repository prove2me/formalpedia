-- Prove2me | solution 1 for GlobalTheory.FinAffineCharts.refineLB_isLB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:04:40.366834+00:00
-- url     : https://prove2.me/submissions/fb52c235-fc71-4ecf-90fc-89272e53de5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteAffineCharts
import Theorems.Thm_GlobalTheory_FinAffineCharts_res_res
import Theorems.Thm_GlobalTheory_FinAffineCharts_cocycle_on

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.FinAffineCharts
variable {X : Scheme.{0}}
namespace GlobalTheory.FinAffineCharts
theorem _root_.solution {L : LB X} (hL : L.IsLB) {κ : Type} (W : κ → X.Opens) (c : κ → L.ι)
    (h : ∀ a, W a ≤ L.U (c a)) (hc : ⨆ a, W a = ⊤) : (refineLB L W c h).IsLB where
  cover := hc
  g_self a := by
    have := congrArg (res (h a)) (hL.g_self (c a))
    rw [res_res, map_one] at this
    exact (res_res _ _ _).trans this
  cocycle a b d :=
    (congrArg₂ (· * ·) (res_res _ _ _) (res_res _ _ _)).trans
      ((cocycle_on hL _ _ _ _ _ _).trans (res_res _ _ _).symm)
end GlobalTheory.FinAffineCharts
