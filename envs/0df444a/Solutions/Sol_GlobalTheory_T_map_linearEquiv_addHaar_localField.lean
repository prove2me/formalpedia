-- Prove2me | solution 1 for GlobalTheory.T.map_linearEquiv_addHaar_localField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:40:13.956395+00:00
-- url     : https://prove2.me/submissions/7f239b69-08c2-4a98-84ef-0b7bd89feba6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapLinearEquivAddHaarLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapLinearEquivAddHaarLocalFieldStatement
import Theorems.Thm_GlobalTheory_KSp_map_linearEquiv_haar


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
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (T : V ≃ₗ[F] V), μ.map T = (distribHaarChar F (LinearEquiv.det T))⁻¹ • μ := by
  first | exact @GlobalTheory.KSp.map_linearEquiv_haar | exact GlobalTheory.KSp.map_linearEquiv_haar | (intros; apply GlobalTheory.KSp.map_linearEquiv_haar <;> assumption)
end _root_.GlobalTheory.T
