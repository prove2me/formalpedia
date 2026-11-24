-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.mulN_eq_mulNat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:57:38.65453+00:00
-- url     : https://prove2.me/submissions/ae257d23-43cd-4be5-bb94-8b54fd862830

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PerfectPairings_mulNat_succ


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
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.FourierChainCompare
theorem _root_.solution (G : FGLaw R d) (n : ℕ) : mulN G n = mulNat G n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [mulN, ih, mulNat_succ]
end GlobalTheory.FourierChainCompare
