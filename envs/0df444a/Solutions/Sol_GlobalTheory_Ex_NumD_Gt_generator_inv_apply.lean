-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Gt.generator_inv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:41:26.829272+00:00
-- url     : https://prove2.me/submissions/b723a2e7-3873-430a-b23a-5ab37620feb2

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
open GlobalTheory.Ex.NumD
variable (N : NumD O)
open GlobalTheory.Ex.NumD.Gt
variable {N}
namespace GlobalTheory.Ex.NumD.Gt
theorem _root_.solution (g : N.Gt) (χ : N.X) : g⁻¹.s χ = N.θ (N.c χ) g.b g.b⁻¹ / g.s χ := rfl
end GlobalTheory.Ex.NumD.Gt
