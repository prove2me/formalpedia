-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.manyChars_iff_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:29:13.849522+00:00
-- url     : https://prove2.me/submissions/8d976cb9-e053-4342-b9c5-8626eba036fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
import Theorems.Thm_GlobalTheory_FourierChainCompare_manyChars_of_perfect
import Theorems.Thm_GlobalTheory_FourierChainCompare_finite_unitChar
import Theorems.Thm_GlobalTheory_FourierChainCompare_perfect_eval

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
theorem _root_.solution (A K : Type) [AddCommGroup A] [Fintype A] [Field K] :
    ManyChars A K ↔ IsPerfectPairing (evalPairing A K) := by
  refine ⟨fun h => perfect_eval h.2, fun h => ?_⟩
  haveI := finite_unitChar A K
  letI := Fintype.ofFinite (Additive (Multiplicative A →* Kˣ))
  exact manyChars_of_perfect h
end GlobalTheory.FourierChainCompare
