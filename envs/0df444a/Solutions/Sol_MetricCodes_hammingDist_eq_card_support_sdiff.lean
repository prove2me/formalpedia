-- Prove2me | solution 1 for MetricCodes.hammingDist_eq_card_support_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/c91b545d-02c9-4fc4-9186-4f8bb0ddc4db

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution {n : ℕ}
    (x y : BinaryWord n) :
    hammingDist x y =
      (wordSupport x \ wordSupport y).card +
      (wordSupport y \ wordSupport x).card := by
  have hsets :
      (Finset.univ.filter fun i => x i ≠ y i) =
        (wordSupport x \ wordSupport y) ∪
        (wordSupport y \ wordSupport x) := by
    ext i
    cases hx : x i <;> cases hy : y i <;>
      simp [wordSupport, hx, hy]
  have hdisj :
      Disjoint (wordSupport x \ wordSupport y)
        (wordSupport y \ wordSupport x) := by
    apply Finset.disjoint_left.mpr
    intro i hxy hyx
    exact (Finset.mem_sdiff.mp hxy).2 (Finset.mem_sdiff.mp hyx).1
  unfold hammingDist
  rw [hsets, Finset.card_union_of_disjoint hdisj]
end MetricCodes
