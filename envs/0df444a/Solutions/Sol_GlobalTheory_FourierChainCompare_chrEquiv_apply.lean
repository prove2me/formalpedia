-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.chrEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:43:49.118162+00:00
-- url     : https://prove2.me/submissions/4bbeec4c-4216-4580-b6d1-822c41a8e5b9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings
open GlobalTheory GlobalTheory.FourierChainCompare
variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K]
variable [Fintype A] [Fintype B]
namespace GlobalTheory.FourierChainCompare
theorem _root_.solution {e : A → B → Kˣ} (he : IsPerfectPairing e) (t : B) :
    chrEquiv he t = chr he t := rfl
end GlobalTheory.FourierChainCompare
