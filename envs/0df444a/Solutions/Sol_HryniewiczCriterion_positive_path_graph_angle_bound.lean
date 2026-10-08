-- Prove2me | solution 1 for HryniewiczCriterion.positive_path_graph_angle_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T20:40:56.735587+00:00
-- url     : https://prove2.me/submissions/c607334b-832b-4413-94cb-6d548742e740

import Theorems.Thm_HryniewiczCriterion_graphUnitary4_positive_path
import Theorems.Thm_HryniewiczCriterion_positive_unitary_path_eigenAngleSum_le
import Theorems.Thm_HryniewiczCriterion_eigenAngleSum_graphUnitary4_blockOne

open HryniewiczCriterion
open scoped ContDiff ComplexOrder

theorem solution (Ŷ S : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (T : ℝ)
    (hT : 0 < T) (hSc : ∀ i j : Fin 4, Continuous fun t => S t i j) (hSpos : ∀ t, (S t).PosDef)
    (h0 : Ŷ 0 = 1)
    (hd : ∀ t : ℝ, ∀ i j : Fin 4, HasDerivAt (fun s => Ŷ s i j) ((symplJ4 * S t * Ŷ t) i j) t)
    (g : Matrix (Fin 2) (Fin 2) ℝ) (hend : Ŷ T = blockOne g) (θ : ℝ → ℝ)
    (hθ : IsDetAngleLift (fun t => graphUnitary4 (Ŷ t)) T θ) :
    4 * Real.pi + eigenAngleSum (graphUnitary2 g) ≤ θ T := by
  -- (C1) the graph unitary path is a positive unitary path starting at the identity
  obtain ⟨hV0, hU, Q, hQ⟩ := graphUnitary4_positive_path Ŷ S hSpos h0 hd
  -- (C2) a positive unitary path winds at least as far as its endpoint eigen-angles
  have hle := positive_unitary_path_eigenAngleSum_le (fun t => graphUnitary4 (Ŷ t)) Q T hT hV0
    (fun t _ => hU t) (fun t _ => (hQ t).1) (fun t _ => (hQ t).2) θ hθ
  -- (C3) at time `T` the two fixed directions contribute `4π`
  have hblock := eigenAngleSum_graphUnitary4_blockOne g
  simp only [hend] at hle
  rw [hblock] at hle
  exact hle
