-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.concaveOn_restrict_nonnegative_interval
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:25:44.872544+00:00
-- url     : https://prove2.me/submissions/02fc96cb-74f0-4917-93b2-c0f7350ab951

import Mathlib

namespace NestedSeatAlloc.IntPolicy

theorem concaveOn_restrict_nonnegative_interval {g : ℝ → ℝ} {a b : ℝ}
    (hg : ConcaveOn ℝ (Set.Ici 0) g) (ha : 0 ≤ a) :
    ConcaveOn ℝ (Set.Icc a b) g := by
  exact hg.subset (fun x hx => le_trans ha hx.1) (convex_Icc a b)

end NestedSeatAlloc.IntPolicy

theorem solution {g : ℝ → ℝ} {a b : ℝ}
    (hg : ConcaveOn ℝ (Set.Ici 0) g) (ha : 0 ≤ a) :
    ConcaveOn ℝ (Set.Icc a b) g := by
  exact hg.subset (fun x hx => le_trans ha hx.1) (convex_Icc a b)

#print axioms solution

