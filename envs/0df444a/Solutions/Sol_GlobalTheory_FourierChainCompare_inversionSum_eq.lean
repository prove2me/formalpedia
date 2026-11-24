-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.inversionSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:50:13.911022+00:00
-- url     : https://prove2.me/submissions/4ecbf3f3-5dd1-4e0c-bbe6-e55e2b672ff9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
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
theorem _root_.solution [Fintype (AddChar A K)] {e : A → B → Kˣ} (he : IsPerfectPairing e)
    (φ : A → K) (a : A) :
    ∑ t : B, IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t * ((e a t : Kˣ) : K) =
      ∑ χ : AddChar A K, ((Fintype.card A : K)⁻¹ * ∑ b, φ b * χ (-b)) * χ a := by
  rw [← Equiv.sum_comp (chrEquiv he)]
  exact Finset.sum_congr rfl fun t _ => by rw [fourierCoeff_eq he]; rfl
end GlobalTheory.FourierChainCompare
