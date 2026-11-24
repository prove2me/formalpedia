-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.manyChars_iff_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:07.400079+00:00
-- url     : https://prove2.me/submissions/8e44b71b-6880-4b22-855f-f30d3500da84

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
    ManyChars A K ↔ ∃ (B : Type) (_ : AddCommGroup B) (_ : Fintype B) (e : A → B → Kˣ),
      IsPerfectPairing e := by
  constructor
  · intro h
    haveI := finite_unitChar A K
    exact ⟨_, inferInstance, Fintype.ofFinite _, _, perfect_eval h.2⟩
  · rintro ⟨B, _, _, e, he⟩
    exact manyChars_of_perfect he
end GlobalTheory.FourierChainCompare
