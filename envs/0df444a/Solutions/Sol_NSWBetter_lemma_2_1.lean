-- Prove2me | solution 1 for NSWBetter.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:29:15.744625+00:00
-- url     : https://prove2.me/submissions/986126d6-63ee-4190-951b-04c458589d2d

import Mathlib

theorem solution {m : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g) (Xi Xj Si Sj : Finset (Fin m))
    (hdisj : Disjoint Xi Xj) (hSi : Si ⊆ Xi) (hSj : Sj ⊆ Xj)
    (h1 : ∑ g ∈ Si, v g ≤ ∑ g ∈ Sj, v g) (h2 : ∑ g ∈ Xj \ Sj, v g ≤ ∑ g ∈ Xi \ Si, v g) :
    (∑ g ∈ (Xi \ Si) ∪ Sj, v g) * (∑ g ∈ (Xj \ Sj) ∪ Si, v g) ≤
        (∑ g ∈ Xi, v g) * (∑ g ∈ Xj, v g) ∧
      ((∑ g ∈ (Xi \ Si) ∪ Sj, v g) * (∑ g ∈ (Xj \ Sj) ∪ Si, v g) =
          (∑ g ∈ Xi, v g) * (∑ g ∈ Xj, v g) ↔
        ∑ g ∈ Sj, v g = ∑ g ∈ Si, v g ∨ ∑ g ∈ Xi \ Si, v g = ∑ g ∈ Xj \ Sj, v g) := by
  have d1 : Disjoint (Xi \ Si) Sj :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset (Finset.disjoint_of_subset_right hSj hdisj)
  have d2 : Disjoint (Xj \ Sj) Si :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right hSi hdisj.symm)
  rw [Finset.sum_union d1, Finset.sum_union d2, ← Finset.sum_sdiff hSi, ← Finset.sum_sdiff hSj]
  generalize ∑ g ∈ Si, v g = a at *
  generalize ∑ g ∈ Sj, v g = b at *
  generalize ∑ g ∈ Xi \ Si, v g = A at *
  generalize ∑ g ∈ Xj \ Sj, v g = B at *
  have key : (A + a) * (B + b) - (A + b) * (B + a) = (A - B) * (b - a) := by ring
  refine ⟨?_, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h1)]
  · constructor
    · intro h
      have h0 : (A - B) * (b - a) = 0 := by linarith
      rcases mul_eq_zero.mp h0 with h3 | h3
      · right; linarith
      · left; linarith
    · rintro (h | h)
      · subst h; ring
      · subst h; ring
