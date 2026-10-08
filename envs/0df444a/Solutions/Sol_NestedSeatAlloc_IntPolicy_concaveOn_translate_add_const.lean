-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.concaveOn_translate_add_const
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:28:55.856279+00:00
-- url     : https://prove2.me/submissions/58b8b080-054b-4019-bc9d-c3a863edda5a

import Mathlib

namespace NestedSeatAlloc.IntPolicy

theorem concaveOn_translate_add_const {g : ℝ → ℝ} {d c : ℝ}
    (hg : ConcaveOn ℝ (Set.Ici 0) g) :
    ConcaveOn ℝ (Set.Ici d) (fun x => c + g (x - d)) := by
  refine ⟨convex_Ici d, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : x - d ∈ Set.Ici (0 : ℝ) := by change 0 ≤ x - d; exact sub_nonneg.mpr hx
  have hy' : y - d ∈ Set.Ici (0 : ℝ) := by change 0 ≤ y - d; exact sub_nonneg.mpr hy
  have h := hg.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have he : a * x + b * y - d = a * (x - d) + b * (y - d) := by
    calc
      _ = a * x + b * y - (a + b) * d := by rw [hab]; ring
      _ = _ := by ring
  have hc : a * c + b * c = c := by
    calc
      _ = (a + b) * c := by ring
      _ = c := by rw [hab]; ring
  rw [he]
  nlinarith only [h, hc]

end NestedSeatAlloc.IntPolicy

theorem solution {g : ℝ → ℝ} {d c : ℝ}
    (hg : ConcaveOn ℝ (Set.Ici 0) g) :
    ConcaveOn ℝ (Set.Ici d) (fun x => c + g (x - d)) := by
  refine ⟨convex_Ici d, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : x - d ∈ Set.Ici (0 : ℝ) := by change 0 ≤ x - d; exact sub_nonneg.mpr hx
  have hy' : y - d ∈ Set.Ici (0 : ℝ) := by change 0 ≤ y - d; exact sub_nonneg.mpr hy
  have h := hg.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have he : a * x + b * y - d = a * (x - d) + b * (y - d) := by
    calc
      _ = a * x + b * y - (a + b) * d := by rw [hab]; ring
      _ = _ := by ring
  have hc : a * c + b * c = c := by
    calc
      _ = (a + b) * c := by ring
      _ = c := by rw [hab]; ring
  rw [he]
  nlinarith only [h, hc]

#print axioms solution
