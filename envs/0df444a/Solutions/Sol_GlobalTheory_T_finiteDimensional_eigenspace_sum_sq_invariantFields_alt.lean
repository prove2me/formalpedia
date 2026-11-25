-- Prove2me | solution 1 for GlobalTheory.T.finiteDimensional_eigenspace_sum_sq_invariantFields_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:53:58.859707+00:00
-- url     : https://prove2.me/submissions/e28b56d9-e22a-4033-94e1-5eadf09d2f3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalEigenspaceSumSqInvariantFieldsA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalEigenspaceSumSqInvariantFieldsAStatement
import Theorems.Thm_GlobalTheory_finiteDimensional_eigenspace_sum_sq_invariantFields


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
theorem _root_.solution : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L] (S : Submodule ℂ (K → ℂ)), (∀ f ∈ S, Continuous f) → ∀ e : L → K, (∀ X : L, Continuous fun t : ℝ => e (t • X)) → e 0 = 1 → (∀ r : ℝ, 0 < r → e '' Metric.ball 0 r ∈ 𝓝 (1 : K)) → ∀ d : L → Module.End ℂ S, (∀ X Y, d (X + Y) = d X + d Y) → (∀ (a : ℝ) X, d (a • X) = (a : ℂ) • d X) → (∀ (X : L) (f : S) (x : K) (t : ℝ), HasDerivAt (fun t : ℝ => f.1 (x * e (t • X))) ((d X f).1 (x * e (t • X))) t) → ∀ (ι : Type) [Fintype ι] (X : ι → L), Submodule.span ℝ (Set.range X) = ⊤ → ∀ lam : ℂ, FiniteDimensional ℂ (Module.End.eigenspace (∑ i, d (X i) * d (X i)) lam) := by
  first | exact @GlobalTheory.finiteDimensional_eigenspace_sum_sq_invariantFields | exact GlobalTheory.finiteDimensional_eigenspace_sum_sq_invariantFields | (intros; apply GlobalTheory.finiteDimensional_eigenspace_sum_sq_invariantFields <;> assumption)
end _root_.GlobalTheory.T
