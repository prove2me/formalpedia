-- Prove2me | solution 1 for GlobalTheory.Ex.tate_vt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:43:57.941945+00:00
-- url     : https://prove2.me/submissions/0dd17e4a-70bd-4520-afb7-fc9f781a5ab4

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
namespace GlobalTheory.Ex
theorem _root_.solution (q : Oˣ) (t : Multiplicative ℤ →* Oˣ) (n : ℤ) :
    (tate q).vt ((tate q).tor t) n = (q ^ n ^ 2 * t (Multiplicative.ofAdd n) : Oˣ) := mul_one _
end GlobalTheory.Ex
