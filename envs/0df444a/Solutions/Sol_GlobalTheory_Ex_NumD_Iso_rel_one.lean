-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Iso.rel_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:43.486047+00:00
-- url     : https://prove2.me/submissions/bb9fc3bd-516d-4e31-937d-da0d38828823

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
namespace Iso
theorem _root_.solution {N' N : NumD O} (I : Iso N' N) : I.Rel 1 1 :=
  ⟨(map_one I.φ).symm, fun χ => by simp [I.h_one]⟩
end Iso
end GlobalTheory.Ex.NumD
