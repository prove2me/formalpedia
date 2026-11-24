-- Prove2me | solution 1 for GlobalTheory.T.exists_schwartzBruhat_convolution_localFieldPower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:08:08.290982+00:00
-- url     : https://prove2.me/submissions/a2c49faa-f449-4d9e-8103-b25e59e1f418

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPowerStatement
import Theorems.Thm_GlobalTheory_SBConv_exists_convolution


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (Φ Ψ : SB (n → k)), ∃ (T : (n → k) → SB (n → k)) (w : SB (n → k)), (∀ y x, (T y).1 x = Ψ.1 (x - y)) ∧ (∀ x, w.1 x = ∫ y, Φ.1 y * Ψ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧ (∀ x, w.1 x = ∫ y, Ψ.1 y * Φ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧ ∀ l : SB (n → k) →ₗ[ℂ] ℂ, l w = ∫ y, Φ.1 y * l (T y) ∂(Measure.pi fun _ => ν) := by
  first | exact @GlobalTheory.SBConv.exists_convolution | exact GlobalTheory.SBConv.exists_convolution | (intros; apply GlobalTheory.SBConv.exists_convolution <;> assumption)
end _root_.GlobalTheory.T
