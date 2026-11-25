-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.or_card_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:43:57.613153+00:00
-- url     : https://prove2.me/submissions/1e1863ac-4689-4b4b-afe8-357a830f2a82

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
variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K] [Fintype A] [Fintype B]
namespace GlobalTheory.FourierChainCompare
theorem _root_.solution (O : Subring K) (n c : K) : (n * c ∈ O ∨ n = 0) ↔ n * c ∈ O :=
  or_iff_left_of_imp fun h => by rw [h, zero_mul]; exact O.zero_mem
end GlobalTheory.FourierChainCompare
