-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.mem_intRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:51:45.262415+00:00
-- url     : https://prove2.me/submissions/64953b71-1d22-4bf6-bafc-0003c0b85a8a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_SiegelFamilyZetaUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit
theorem _root_.solution {C : Type} [NormedField C] [IsUltrametricDist C] (x : C) : x ∈ intRing C ↔ ‖x‖ ≤ 1 := by
  simp [intRing, Valuation.mem_valuationSubring_iff]
  exact ge_iff_le
end GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit
