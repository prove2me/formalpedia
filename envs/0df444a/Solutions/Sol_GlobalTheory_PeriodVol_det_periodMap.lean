-- Prove2me | solution 1 for GlobalTheory.PeriodVol.det_periodMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:24:33.546328+00:00
-- url     : https://prove2.me/submissions/613faa4d-8fcb-4ee2-87ff-93129a436b06

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
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) :
    LinearMap.det (periodMap τ) = (τ.map Complex.im).det := by
  rw [periodMap, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, _root_.one_mul]
end GlobalTheory.PeriodVol
