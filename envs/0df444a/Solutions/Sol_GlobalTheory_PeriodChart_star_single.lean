-- Prove2me | solution 1 for GlobalTheory.PeriodChart.star_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:43.656907+00:00
-- url     : https://prove2.me/submissions/92e43dc5-db02-457f-80e8-990d3eda69e5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction

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
theorem _root_.solution (k : Fin g) : star (Pi.single k (1 : ℂ) : Fin g → ℂ) = Pi.single k 1 := by
  funext i
  by_cases h : i = k
  · subst h; simp
  · simp [h]
end GlobalTheory.PeriodChart
