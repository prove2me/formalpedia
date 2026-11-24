-- Prove2me | solution 1 for GlobalTheory.Ex.Level3.cube_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:44:42.592377+00:00
-- url     : https://prove2.me/submissions/98efc4c3-61b4-4c9c-a706-4ad1ce058405

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
attribute [instance] NumB.grp
attribute [instance] NumD.add NumD.free NumD.fin
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.Level3
namespace GlobalTheory.Ex.Level3
theorem _root_.solution : ∀ b : A₃, (∀ b', cubN cube 3 1 b' b / cubN cube 3 1 b b' = 1) → b = 1 := by
  simp only [cubN, Finset.prod_range_succ, Finset.prod_range_zero]
  decide +kernel
end GlobalTheory.Ex.Level3
