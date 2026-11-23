-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.tor_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:24.851547+00:00
-- url     : https://prove2.me/submissions/fad01098-84d9-4429-88de-37b281f94d39

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
theorem _root_.solution : Function.Injective N.tor := fun t t' h =>
  MonoidHom.ext fun χ => congrArg (fun g : N.Gt => g.s χ.toAdd) h
end GlobalTheory.Ex.NumD
