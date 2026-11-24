-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.chr_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:09:40.664207+00:00
-- url     : https://prove2.me/submissions/687c1770-ee75-44a9-ac81-7dbbeafca01a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
import Theorems.Thm_GlobalTheory_FourierChainCompare_chr_apply

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
namespace GlobalTheory.FourierChainCompare
theorem _root_.solution {e : A → B → Kˣ} (he : IsPerfectPairing e) (t : B) (a : A) :
    chr he t (-a) = (((e a t)⁻¹ : Kˣ) : K) := by
  rw [AddChar.map_neg_eq_inv, chr_apply, Units.val_inv_eq_inv_val]
end GlobalTheory.FourierChainCompare
