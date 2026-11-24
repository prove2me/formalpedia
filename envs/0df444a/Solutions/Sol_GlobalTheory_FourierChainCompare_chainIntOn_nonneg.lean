-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.chainIntOn_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:58:34.494479+00:00
-- url     : https://prove2.me/submissions/efb2568d-ac22-47be-96b5-4acfd4a17a81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
import Theorems.Thm_GlobalTheory_FourierChainCompare_chainInt_natCast_iff

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
theorem _root_.solution (H : NChainSt) : ChainIntOn {n | 0 ≤ n} := by
  intro R _ d G O _ A ι _ u P k hP n hn f
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  exact (chainInt_natCast_iff A u P k m f).mp (H R d G m u P k hP f)
end GlobalTheory.FourierChainCompare
