-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.tor_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:41:49.069701+00:00
-- url     : https://prove2.me/submissions/133eb8ad-3e3f-481d-94d6-bfd67492accc

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
namespace GlobalTheory.Ex.NumD
theorem _root_.solution (t : Multiplicative N.X →* Oˣ) : N.tor t⁻¹ = (N.tor t)⁻¹ := N.torHom.map_inv t
end GlobalTheory.Ex.NumD
