-- Prove2me | solution 1 for GlobalTheory.PeriodChart.sesq_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:22.446273+00:00
-- url     : https://prove2.me/submissions/67d903e1-c817-40c4-872d-60c7eb822712

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
theorem _root_.solution (G : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : sesq G z w = hermForm G z w := rfl
end GlobalTheory.PeriodChart
