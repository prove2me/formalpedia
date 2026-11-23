-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.qEq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:19.529096+00:00
-- url     : https://prove2.me/submissions/08d0d95c-3cf1-4469-9c01-fc1566b99f60

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
theorem _root_.solution {k : ℕ} (p p' : N.QT k) : N.QEq p p' ↔ ∃ z, p' = p * N.qTriv k z :=
  exists_congr fun _ => ⟨fun h => Subtype.ext (Prod.ext h.1 h.2),
    fun h => ⟨congrArg (fun q : N.QT k => q.1.1.toAdd) h, congrArg (fun q : N.QT k => q.1.2) h⟩⟩
end GlobalTheory.Ex.NumD
