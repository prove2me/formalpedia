-- Prove2me | solution 1 for GlobalTheory.T.isSelfDualCompactOpenGroup_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:14:40.760273+00:00
-- url     : https://prove2.me/submissions/d92b04fb-af6e-4f18-960b-4367bb2823e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompactOpenSubgroupExhaustion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompactOpenSubgroupExhaustionStatement
import Theorems.Thm_GlobalTheory_KSp_good_of_finiteDimensional


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V] [IsModuleTopology F V], Good V := by
  first | exact @GlobalTheory.KSp.good_of_finiteDimensional | exact GlobalTheory.KSp.good_of_finiteDimensional | (intros; apply GlobalTheory.KSp.good_of_finiteDimensional <;> assumption)
end _root_.GlobalTheory.T
