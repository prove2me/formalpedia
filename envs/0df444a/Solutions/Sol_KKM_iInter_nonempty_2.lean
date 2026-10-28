-- Prove2me | solution 2 for KKM.iInter_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T04:09:41.815997+00:00
-- url     : https://prove2.me/submissions/7715103b-71df-4e8c-a88c-50030b9b6d33

import Mathlib
import Theorems.Thm_KKM_exists_mem_convexHull_mem_iInter

-- carved verbatim out of submission 818ed08f-1f44-45cc-90a9-3239f8bb6e07, lines 913-924

section

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (n : ℕ) (a : Fin (n + 1) → E)
    (A : Fin (n + 1) → Set E)
    (hA : ∀ i, IsOpen (A i))
    (hcov : convexHull ℝ (Set.range a) ⊆ ⋃ i, A i)
    (hconv : ∀ i, Convex ℝ (convexHull ℝ (Set.range a) \ A i))
    (hv : ∀ i j, i ≠ j → a i ∉ A j) :
    (⋂ i, A i).Nonempty := by
  obtain ⟨z, _, hz⟩ := KKM.exists_mem_convexHull_mem_iInter n a A hA hcov hconv hv
  exact ⟨z, Set.mem_iInter.2 hz⟩

end
