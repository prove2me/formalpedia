-- Prove2me | solution 1 for GlobalTheory.RowLaw.ShiftSum.coeff_tyS_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:47:01.482665+00:00
-- url     : https://prove2.me/submissions/d6b06a67-19d7-44ff-a7a4-a3af7d34278b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedCurveLogarithmsClosedUnderTadicLimitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ShiftedSumMemTypicalCurveSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.ShiftSum
variable {C : Type} [Field C]
namespace GlobalTheory.RowLaw.ShiftSum
theorem _root_.solution (l m : ℕ) {a b : ℕ → C} (h : ∀ s ≤ m, a s = b s) :
    PowerSeries.coeff m (tyS l a) = PowerSeries.coeff m (tyS l b) := by
  unfold tyS
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [h s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))]
end GlobalTheory.RowLaw.ShiftSum
