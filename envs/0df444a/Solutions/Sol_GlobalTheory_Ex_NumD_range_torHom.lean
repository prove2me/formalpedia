-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.range_torHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:41:43.599832+00:00
-- url     : https://prove2.me/submissions/ad8cd4c2-d33d-4621-be00-232b2d15ac26

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
theorem _root_.solution : N.torHom.range = N.projB.ker := Subgroup.ext fun g => N.exists_tor_iff g
end GlobalTheory.Ex.NumD
