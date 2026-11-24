-- Prove2me | solution 1 for GlobalTheory.norm_sq_toLp_two_eq_integral_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:28:12.760497+00:00
-- url     : https://prove2.me/submissions/fde76014-d558-4b78-9b32-b2b0d60ef763

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalOfUniformlyAlmostInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (g : C(K, ℂ)) :
    ‖ContinuousMap.toLp 2 μ ℂ g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by
  have h := ContinuousMap.inner_toLp μ g g
  rw [inner_self_eq_norm_sq_to_K] at h
  simp_rw [Complex.mul_conj'] at h
  have h2 : (∫ x, ((‖g x‖ : ℂ)) ^ 2 ∂μ) = ((∫ x, ‖g x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; simp
  rw [h2] at h
  apply Complex.ofReal_injective
  rw [← h, Complex.ofReal_pow]
  rfl
end GlobalTheory
