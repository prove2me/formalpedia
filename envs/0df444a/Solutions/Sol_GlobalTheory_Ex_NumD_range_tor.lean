-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.range_tor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:49:24.5144+00:00
-- url     : https://prove2.me/submissions/ad53897b-3630-4fe4-9085-416e0e3b678c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Theorems.Thm_GlobalTheory_Ex_NumD_exists_tor_iff

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
namespace GlobalTheory.Ex.NumD
theorem _root_.solution : Set.range N.tor = {g | g.b = 1} := Set.ext fun g => N.exists_tor_iff g
end GlobalTheory.Ex.NumD
