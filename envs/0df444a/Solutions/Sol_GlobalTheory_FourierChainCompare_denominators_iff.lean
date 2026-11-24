-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.denominators_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:50:13.240918+00:00
-- url     : https://prove2.me/submissions/4d6b53ae-2d22-4f1e-b9cb-dd4aad691e21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
import Theorems.Thm_GlobalTheory_FourierChainCompare_card_ne_zero_of_perfect
import Theorems.Thm_GlobalTheory_FourierChainCompare_fourierCoeff_eq

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
theorem _root_.solution {e : A → B → Kˣ} (he : IsPerfectPairing e) (O : Subring K) (φ : A → K)
    (t : B) :
    ((Fintype.card A : K) * ((Fintype.card A : K)⁻¹ * ∑ b, φ b * chr he t (-b)) ∈ O ∨
      (Fintype.card A : K) = 0) ↔ ((Fintype.card B : ℕ) : K) * IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t ∈ O := by
  rw [or_iff_left (card_ne_zero_of_perfect he), fourierCoeff_eq he, card_eq_of_perfect he]
end GlobalTheory.FourierChainCompare
