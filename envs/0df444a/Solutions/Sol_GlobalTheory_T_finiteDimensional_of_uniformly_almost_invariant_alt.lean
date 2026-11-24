-- Prove2me | solution 1 for GlobalTheory.T.finiteDimensional_of_uniformly_almost_invariant_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:41:26.348109+00:00
-- url     : https://prove2.me/submissions/a83645c8-05c9-444b-a286-2482c1a32d03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalOfUniformlyAlmostInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalOfUniformlyAlmostInvariantStatement
import Theorems.Thm_GlobalTheory_finiteDimensional_of_uniformly_almost_invariant


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (E : Submodule ℂ (K → ℂ)), (∀ f ∈ E, Continuous f) → ∀ U ∈ 𝓝 (1 : K), (∀ f ∈ E, ∀ u ∈ U, ∫ x, ‖f (x * u) - f x‖ ^ 2 ∂μ ≤ (1 / 4) * ∫ x, ‖f x‖ ^ 2 ∂μ) → FiniteDimensional ℂ E := by
  first | exact @GlobalTheory.finiteDimensional_of_uniformly_almost_invariant | exact GlobalTheory.finiteDimensional_of_uniformly_almost_invariant | (intros; apply GlobalTheory.finiteDimensional_of_uniformly_almost_invariant <;> assumption)
end _root_.GlobalTheory.T
