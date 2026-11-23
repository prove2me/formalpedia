-- Prove2me | solution 1 for GlobalTheory.PeriodVol.reImCoord_symm_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:48.487565+00:00
-- url     : https://prove2.me/submissions/332077ff-ff51-4c35-8b21-f6b1399e67e8

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
theorem _root_.solution {g : ℕ} (p : Fin g ⊕ Fin g → ℝ) (i : Fin g) :
    ((reImCoord g).symm p i).re = p (Sum.inl i) := rfl
end GlobalTheory.PeriodVol
