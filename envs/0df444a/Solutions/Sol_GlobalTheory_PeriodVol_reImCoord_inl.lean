-- Prove2me | solution 1 for GlobalTheory.PeriodVol.reImCoord_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:47.796122+00:00
-- url     : https://prove2.me/submissions/a7ae5bc7-1e61-4d99-b9f9-310d9a0c3e11

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_VolumeFundamentalDomainPeriodLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodVol
namespace GlobalTheory.PeriodVol
theorem _root_.solution {g : ℕ} (z : Fin g → ℂ) (i : Fin g) : reImCoord g z (Sum.inl i) = (z i).re := rfl
end GlobalTheory.PeriodVol
