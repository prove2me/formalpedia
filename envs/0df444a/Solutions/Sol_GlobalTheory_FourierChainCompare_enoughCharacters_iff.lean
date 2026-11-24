-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.enoughCharacters_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:48:49.281422+00:00
-- url     : https://prove2.me/submissions/62cfd1e7-acff-4a7f-af03-7ef792300f49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
import Theorems.Thm_GlobalTheory_FourierChainCompare_finite_unitChar
import Theorems.Thm_GlobalTheory_FourierChainCompare_manyChars_iff_eval

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
theorem _root_.solution : EnoughCharacters ↔
    ∀ (A K : Type) [AddCommGroup A] [Fintype A] [Field K]
      [HasEnoughRootsOfUnity K (AddMonoid.exponent A)], ManyChars A K :=
  ⟨fun H A K _ _ _ _ => (manyChars_iff_eval A K).mpr (H A K).2,
    fun H A K _ _ _ _ => ⟨finite_unitChar A K, (manyChars_iff_eval A K).mp (H A K)⟩⟩
end GlobalTheory.FourierChainCompare
