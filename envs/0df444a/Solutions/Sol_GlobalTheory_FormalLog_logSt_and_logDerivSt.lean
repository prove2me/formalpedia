-- Prove2me | solution 1 for GlobalTheory.FormalLog.logSt_and_logDerivSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:20:38.005082+00:00
-- url     : https://prove2.me/submissions/6e019e9b-63a7-4b82-b246-01ac52c6ffd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PderivSecondEvFirstPointEqZero
import Theorems.Thm_GlobalTheory_FormalLog_logSt
import Theorems.Thm_GlobalTheory_FormalLog_logDerivSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
variable [Algebra ℚ k]
namespace GlobalTheory.FormalLog
theorem _root_.solution : LogSt ∧ LogDerivSt := ⟨logSt, logDerivSt⟩
end GlobalTheory.FormalLog
