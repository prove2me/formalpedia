-- Prove2me | solution 1 for LeanEval.Geometry.WhitneyEmbeddingProblem.whitney_embedding
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T11:49:38.950106+00:00
-- url     : https://prove2.me/submissions/59611d86-133a-4b4e-9eba-77edae3fa053
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WhitneyEmbedding_compact_weak_embedding
import Theorems.Thm_WhitneyEmbedding_weak_embedding_of_finite_immersion_and_proper_function
import Theorems.Thm_WhitneyEmbedding_finite_immersion_and_proper_function_of_noncompact
import Theorems.Thm_WhitneyEmbedding_strong_embedding_from_closed_weak_embedding

open scoped Manifold ContDiff
open Topology

/-- Exact strong Whitney mission target. The two geometric dependencies remain explicit. -/
theorem solution (n : ℕ) (_hn : 1 ≤ n)
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ e ∧
      IsEmbedding e ∧
      ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) := by
  classical
  by_cases hc : CompactSpace M
  · let : CompactSpace M := hc
    obtain ⟨e, he, hei, hed⟩ := WhitneyEmbedding.compact_weak_embedding n (M := M)
    exact WhitneyEmbedding.strong_embedding_from_closed_weak_embedding n _hn e he hei hed
  · obtain ⟨N, e, r, he, hei, hed, hr, hrp⟩ :=
      WhitneyEmbedding.finite_immersion_and_proper_function_of_noncompact n hc
    obtain ⟨g, hg, hgi, hgd⟩ :=
      WhitneyEmbedding.weak_embedding_of_finite_immersion_and_proper_function n N e he hei hed r hr hrp
    exact WhitneyEmbedding.strong_embedding_from_closed_weak_embedding n _hn g hg hgi hgd

#print axioms solution
