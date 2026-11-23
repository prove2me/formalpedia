-- Prove2me | solution 1 for GlobalTheory.AbLaw.isLB_pw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:51.425814+00:00
-- url     : https://prove2.me/submissions/11ff3b03-1dfe-48f7-b84b-32b6a43c3857

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R : Type} [CommRing R]
namespace GlobalTheory.AbLaw
theorem _root_.solution {H : LB X} (hH : H.IsLB) (t : ℤ) : (pw H t).IsLB where
  cover := hH.cover
  g_self := fun i => by
    have h := congrArg (· ^ t) (hH.g_self i)
    simp only [one_zpow, ← map_zpow] at h
    exact h
  cocycle := fun i j k => by
    have h := congrArg (· ^ t) (hH.cocycle i j k)
    simp only [mul_zpow, ← map_zpow] at h
    exact h
end GlobalTheory.AbLaw
