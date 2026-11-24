-- Prove2me | solution 1 for GlobalTheory.PeriodChart.sesq_mulVec_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:24:34.002383+00:00
-- url     : https://prove2.me/submissions/3e5253da-350f-4a44-9f2a-4d9d19daed92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
import Theorems.Thm_GlobalTheory_PeriodChart_sesq_apply
import Theorems.Thm_P2M_GlobalTheory_PeriodChart_star_mulVec__98f0c4b56c3f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {g : ℕ}
namespace GlobalTheory.PeriodChart
theorem _root_.solution (G A : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    sesq G z (A *ᵥ w) = sesq (G * A.map (starRingEnd ℂ)) z w := by
  rw [sesq_apply, sesq_apply, hermForm, hermForm, star_mulVec', mulVec_mulVec]
end GlobalTheory.PeriodChart
