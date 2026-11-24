-- Prove2me | solution 1 for GlobalTheory.KSp.GoodSpace.cball_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:24:38.162987+00:00
-- url     : https://prove2.me/submissions/0fd4fc30-35f2-4c51-9f3f-7a4e13c8b1dc

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompactOpenSubgroupExhaustion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.GoodSpace
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.KSp.GoodSpace
theorem _root_.solution {s t : Fˣ} (h : valuation F (s : F) ≤ valuation F (t : F)) : cball s ⊆ cball t :=
  fun x hx => show valuation F x ≤ valuation F (t : F) from le_trans hx h
end GlobalTheory.KSp.GoodSpace
