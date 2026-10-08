-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.conditional_affine_region_concavity
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:27:09.879989+00:00
-- url     : https://prove2.me/submissions/ee1eb6d5-b189-4bcb-bbfe-9fee7e23d0e9

import Mathlib

namespace NestedSeatAlloc.IntPolicy

theorem conditional_affine_region_concavity {s : Set ℝ} (hs : Convex ℝ s) (m c : ℝ) :
    ConcaveOn ℝ s (fun x => m * x + c) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  apply le_of_eq
  calc
    a * (m * x + c) + b * (m * y + c) = m * (a * x + b * y) + (a + b) * c := by ring
    _ = m * (a * x + b * y) + c := by rw [hab]; ring

end NestedSeatAlloc.IntPolicy

theorem solution {s : Set ℝ} (hs : Convex ℝ s) (m c : ℝ) :
    ConcaveOn ℝ s (fun x => m * x + c) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  apply le_of_eq
  calc
    a * (m * x + c) + b * (m * y + c) = m * (a * x + b * y) + (a + b) * c := by ring
    _ = m * (a * x + b * y) + c := by rw [hab]; ring

#print axioms solution
