-- Prove2me | solution 1 for GlobalTheory.SBConv.exists_convolution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:47:02.054011+00:00
-- url     : https://prove2.me/submissions/9e3fde3f-5c0a-4ddf-a2b7-946c65789cfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsWeakIntegralOfIsLocallyConstantOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower
import Theorems.Thm_GlobalTheory_SBConv_exists_conv
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
noncomputable section
open GlobalTheory GlobalTheory.SBConv
namespace GlobalTheory.SBConv
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (Φ Ψ : SB (n → k)), ∃ (T : (n → k) → SB (n → k)) (w : SB (n → k)), (∀ y x, (T y).1 x = Ψ.1 (x - y)) ∧ (∀ x, w.1 x = ∫ y, Φ.1 y * Ψ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧ (∀ x, w.1 x = ∫ y, Ψ.1 y * Φ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧ ∀ l : SB (n → k) →ₗ[ℂ] ℂ, l w = ∫ y, Φ.1 y * l (T y) ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ n _ _ ν _ Φ Ψ
  have : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  have : T2Space k := GlobalTheory.SplitWeil.t2Space k
  have : ν.Regular := inferInstance
  have : ν.IsNegInvariant := inferInstance
  obtain ⟨w, hw1, hw2⟩ := exists_conv (Measure.pi fun _ : n => ν) Φ Ψ
  refine ⟨translate Ψ, w, fun y x => rfl, hw1, fun x => ?_, hw2⟩
  rw [hw1 x]
  have h := integral_sub_left_eq_self (fun y => Φ.1 (x - y) * Ψ.1 y) (Measure.pi fun _ : n => ν) x
  simp only [sub_sub_cancel] at h
  refine h.trans ?_
  congr 1
  funext y
  exact mul_comm _ _
end GlobalTheory.SBConv
