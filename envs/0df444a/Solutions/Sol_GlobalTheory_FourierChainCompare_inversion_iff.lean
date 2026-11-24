-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.inversion_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:10:17.458879+00:00
-- url     : https://prove2.me/submissions/75aad1f2-b558-4428-a6af-62c5a3b66cee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
import Theorems.Thm_GlobalTheory_FourierChainCompare_inversionSum_eq

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
theorem _root_.solution [Fintype (AddChar A K)] {e : A → B → Kˣ} (he : IsPerfectPairing e)
    (φ : A → K) (a : A) :
    (φ a = ∑ χ : AddChar A K, ((Fintype.card A : K)⁻¹ * ∑ b, φ b * χ (-b)) * χ a) ↔
      φ a = ∑ t : B, IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t * ((e a t : Kˣ) : K) := by
  rw [inversionSum_eq he]
end GlobalTheory.FourierChainCompare
