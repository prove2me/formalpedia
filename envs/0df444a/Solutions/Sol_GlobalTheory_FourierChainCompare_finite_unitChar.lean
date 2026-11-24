-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.finite_unitChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:57:34.789005+00:00
-- url     : https://prove2.me/submissions/e6ca8e3d-ada1-4ba5-aa1a-e114c898cbac

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring

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
    Finite (Additive (Multiplicative A →* Kˣ)) :=
  haveI := finite_addChar A K
  Finite.of_equiv (AddChar A K)
    ((AddChar.toMonoidHomEquiv.trans MonoidHom.toHomUnitsMulEquiv.toEquiv).trans Additive.ofMul)
end GlobalTheory.FourierChainCompare
