-- Prove2me | solution 1 for GlobalTheory.PeriodChart.anti_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:21:22.368513+00:00
-- url     : https://prove2.me/submissions/5802961c-eb1c-4fde-8f99-ce87c72905a9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
import Theorems.Thm_GlobalTheory_PeriodChart_anti_apply
import Theorems.Thm_GlobalTheory_PeriodChart_star_single

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
theorem _root_.solution {Z Z' : Matrix (Fin g) (Fin g) ℂ} (h : ∀ z, anti Z z = anti Z' z) : Z = Z' := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [anti_apply, star_single, mulVec, dotProduct, Pi.single_apply] using this
end GlobalTheory.PeriodChart
