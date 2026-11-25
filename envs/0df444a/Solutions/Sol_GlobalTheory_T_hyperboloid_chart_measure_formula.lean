-- Prove2me | solution 1 for GlobalTheory.T.hyperboloid_chart_measure_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:20:37.103282+00:00
-- url     : https://prove2.me/submissions/160f06fd-68ee-48c2-a2d2-f05f58b60910

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidChartMeasureFormula
import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidChartMeasureFormulaStatement
import Theorems.Thm_GlobalTheory_HypChartPf_hypChart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : PI.RhsWLim.W.HypChart := by
  first | exact @GlobalTheory.HypChartPf.hypChart | exact GlobalTheory.HypChartPf.hypChart | (intros; apply GlobalTheory.HypChartPf.hypChart <;> assumption)
end _root_.GlobalTheory.T
