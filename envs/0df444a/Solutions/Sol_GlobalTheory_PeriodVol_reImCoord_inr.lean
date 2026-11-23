-- Prove2me | solution 1 for GlobalTheory.PeriodVol.reImCoord_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:47.910546+00:00
-- url     : https://prove2.me/submissions/f2048322-b340-4f6d-9992-fd6c74c7535d

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
theorem _root_.solution {g : ℕ} (z : Fin g → ℂ) (i : Fin g) : reImCoord g z (Sum.inr i) = (z i).im := rfl
end GlobalTheory.PeriodVol
