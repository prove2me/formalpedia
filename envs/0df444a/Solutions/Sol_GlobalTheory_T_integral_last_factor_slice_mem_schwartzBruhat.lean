-- Prove2me | solution 1 for GlobalTheory.T.integral_last_factor_slice_mem_schwartzBruhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:15:02.274522+00:00
-- url     : https://prove2.me/submissions/a512ec37-8ca1-45f9-9786-ede1928304df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralLastFactorSliceMemSchwartzBruhat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralLastFactorSliceMemSchwartzBruhatStatement
import Theorems.Thm_GlobalTheory_SliceIntegral_integral_slice_mem_SB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (fun x => ∫ a, Φ.1 (x, 0, a) ∂(Measure.pi fun _ => ν)) ∈ SB (I₀ → k) := by
  first | exact @GlobalTheory.SliceIntegral.integral_slice_mem_SB | exact GlobalTheory.SliceIntegral.integral_slice_mem_SB | (intros; apply GlobalTheory.SliceIntegral.integral_slice_mem_SB <;> assumption)
end _root_.GlobalTheory.T
