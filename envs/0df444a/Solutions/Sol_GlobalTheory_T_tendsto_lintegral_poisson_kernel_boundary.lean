-- Prove2me | solution 1 for GlobalTheory.T.tendsto_lintegral_poisson_kernel_boundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:33:44.549929+00:00
-- url     : https://prove2.me/submissions/a23007e8-dec9-4baa-a337-7870caf2a4ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TendstoLintegralPoissonKernelBoundary
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TendstoLintegralPoissonKernelBoundaryStatement
import Theorems.Thm_GlobalTheory_tendsto_lintegral_concKernel_mul_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M] (ν : Measure M) (K : Set M) (v D : M → ℝ) (C : ENNReal),
    IsCompact K → ContinuousOn v K → ContinuousOn D K → (∀ z ∈ K, v z = 1 → D z = 0) → C ≠ ⊤ →
    Measure.map v (ν.restrict K) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) →
    Filter.Tendsto (fun t : ℝ => ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2 * D z) ∂ν) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  first | exact @GlobalTheory.tendsto_lintegral_concKernel_mul_zero | exact GlobalTheory.tendsto_lintegral_concKernel_mul_zero | (intros; apply GlobalTheory.tendsto_lintegral_concKernel_mul_zero <;> assumption)
end _root_.GlobalTheory.T
