-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.nChain_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:12:34.459964+00:00
-- url     : https://prove2.me/submissions/b49308e2-3b26-4493-87e5-18efc093a7a3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
import Theorems.Thm_GlobalTheory_FourierChainCompare_mulN_eq_mulNat

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
theorem _root_.solution : NChainSt ↔ ChainNat := by
  constructor
  · intro H R _ d G ι _ u P k hP n f
    rw [← mulN_eq_mulNat]
    exact H R d G n u P k hP f
  · intro H R _ d G n ι _ u P k hP f
    rw [mulN_eq_mulNat]
    exact H R d G ι u P k hP n f
end GlobalTheory.FourierChainCompare
