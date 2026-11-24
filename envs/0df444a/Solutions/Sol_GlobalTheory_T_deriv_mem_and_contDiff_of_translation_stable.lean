-- Prove2me | solution 1 for GlobalTheory.T.deriv_mem_and_contDiff_of_translation_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:40:32.85032+00:00
-- url     : https://prove2.me/submissions/c609bd2b-b0f0-48e9-929c-9e4c93c87437

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SmoothOfFiniteDimensionalTranslationStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SmoothOfFiniteDimensionalTranslationStableStatement
import Theorems.Thm_GlobalTheory_smooth_of_finiteDimensional_translation_stable


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
theorem _root_.solution : ∀ (G : Type) [Group G] (M : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ M] (ι : Type) (c : ι → ℝ → G), (∀ i s t, c i (s + t) = c i s * c i t) → (∀ i t, ∀ f ∈ M, (fun g => f (g * c i t)) ∈ M) → (∀ i, ∀ f ∈ M, ∀ g, Continuous fun t : ℝ => f (g * c i t)) → (∀ i, ∀ f ∈ M, (fun g => deriv (fun t : ℝ => f (g * c i t)) 0) ∈ M) ∧ ∀ (k : ℕ) (I : Fin k → ι), ∀ f ∈ M, ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun a => c (I a) (t a)).prod) := by
  first | exact @GlobalTheory.smooth_of_finiteDimensional_translation_stable | exact GlobalTheory.smooth_of_finiteDimensional_translation_stable | (intros; apply GlobalTheory.smooth_of_finiteDimensional_translation_stable <;> assumption)
end _root_.GlobalTheory.T
