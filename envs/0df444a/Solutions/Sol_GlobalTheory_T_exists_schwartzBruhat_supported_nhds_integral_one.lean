-- Prove2me | solution 1 for GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:22:02.42005+00:00
-- url     : https://prove2.me/submissions/e6a1ba98-edfb-4a6b-b0da-4ea95969a228

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatSupportedNhdsIntegralOne
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatSupportedNhdsIntegralOneStatement
import Theorems.Thm_GlobalTheory_RootEx_exists_SB_supported_integral_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (U : Set (n → k)) (_ : U ∈ nhds (0 : n → k)), ∃ Ψ : SB (n → k), (∀ y, y ∉ U → Ψ.1 y = 0) ∧ ∫ y, Ψ.1 y ∂(Measure.pi fun _ => ν) = 1 := by
  first | exact @GlobalTheory.RootEx.exists_SB_supported_integral_one | exact GlobalTheory.RootEx.exists_SB_supported_integral_one | (intros; apply GlobalTheory.RootEx.exists_SB_supported_integral_one <;> assumption)
end _root_.GlobalTheory.T
