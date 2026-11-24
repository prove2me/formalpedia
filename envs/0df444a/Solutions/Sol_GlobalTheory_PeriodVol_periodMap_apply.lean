-- Prove2me | solution 1 for GlobalTheory.PeriodVol.periodMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:24:34.771065+00:00
-- url     : https://prove2.me/submissions/4d66783c-485b-40b8-b82a-c848a51eafb9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_VolumeFundamentalDomainPeriodLattice
import Theorems.Thm_GlobalTheory_PeriodVol_reImCoord_inl
import Theorems.Thm_GlobalTheory_PeriodVol_reImCoord_inr
import Theorems.Thm_GlobalTheory_PeriodVol_reImCoord_symm_re
import Theorems.Thm_GlobalTheory_PeriodVol_reImCoord_symm_im
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.PeriodVol.reImCoord_inl
attribute [local simp] GlobalTheory.PeriodVol.reImCoord_inr
attribute [local simp] GlobalTheory.PeriodVol.reImCoord_symm_re
attribute [local simp] GlobalTheory.PeriodVol.reImCoord_symm_im

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodVol
namespace GlobalTheory.PeriodVol
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    periodMap τ z = (fun i => ((z i).re : ℂ)) + τ.mulVec (fun i => ((z i).im : ℂ)) := by
  ext i
  apply Complex.ext <;>
    simp [periodMap, Matrix.mulVec, dotProduct, Matrix.one_apply]
end GlobalTheory.PeriodVol
